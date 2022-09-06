// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define LC_TOKEN_SIZE 16

static dif_lc_ctrl_t lc;

// LC exit token value for LC state transition.
// Use `volatile` type here because this variable will be overwritten by SV
// testbench via `sw_symbol_backdoor_overwrite` function.
// The SV testbench will encode the actual token value from randomly generated
// OTP token image.
static volatile const uint8_t kLcExitToken[LC_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

OTTF_DEFINE_TEST_CONFIG();

/**
 * Tests the kmac reset won't affect LC state transition.
 *
 * 1) OTP pre-load image with lc_count = `8`.
 * 2) Backdoor write OTP's LC partition to `TestUnlocked1` state, and backdoor
 * write OTP's `test_exit` token and `test_unlock` token to match the rand
 * patterns.
 * 3) Write a wrong KMAC exit token and trigger a LC state transition request
 * to the DEV state.
 * 4) In SV test sequence, wait until LC sends a kmac data
 * request by probing LC_CTRL's `kmac_data_o` pin.
 * 5) In SV test sequence, issue a reset in KMAC block by forcing the rv_dm's
 * `ndmreset_req_o` pin, and it should reset the sys domain IPs only, which does
 * not include LC_CTRL. We expect to see LC_CTRL sends another KMAC data request
 * after the sys domain reset is deasserted.
 * 6) In SV test sequence, wait until KMAC handshake completes, then issue
 * another sys domain reset. Check if the `status.token_error` bit is set and LC
 * state transition is not successfuly.
 * 7) Reset the chip.
 *
 * Then repeat the above steps but load the correct exit token. After the two
 * KMAC resets, this time the testbench expects the LC state transition
 * completes without any error.
 *
 * In summary, this sequence walks through the following LC states:
 * "TestUnlocked1", count = 8 -> "TestUnlocked1", count = 9 -> "Dev", count = 10
 */

bool test_main(void) {
  LOG_INFO("Start initialization.");
  // Device init.
  mmio_region_t lc_reg = mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_lc_ctrl_init(lc_reg, &lc));

  // Get LC count.
  uint8_t lc_count;
  CHECK_DIF_OK(dif_lc_ctrl_get_attempts(&lc, &lc_count));
  LOG_INFO("LC_COUNT is %0d.", lc_count);

  dif_lc_ctrl_token_t token;
  switch (lc_count) {
    case 8:
      // Write incorrect token data and expect the LC transition to fail.
      for (int i = 0; i < LC_TOKEN_SIZE; i++) {
        token.data[i] = kLcExitToken[i] - 1;
      }
      lc_ctrl_testutils_check_lc_state(&lc, kDifLcCtrlStateTestUnlocked1);
      break;
    case 9:
      // Write correct token data and expect the LC transition to pass.
      for (int i = 0; i < LC_TOKEN_SIZE; i++) {
        token.data[i] = kLcExitToken[i];
      }
      lc_ctrl_testutils_check_lc_state(&lc, kDifLcCtrlStateTestUnlocked1);
      break;
    case 10:
      // Check if current status is correct then exit the test.
      lc_ctrl_testutils_check_lc_state(&lc, kDifLcCtrlStateDev);
      return true;
    default:
      // Unexpected value, exit test with error.
      LOG_ERROR("Unexpected lc_count value %0d", lc_count);
      return false;
  }

  // Trigger LC transition request
  CHECK_DIF_OK(dif_lc_ctrl_mutex_try_acquire(&lc));
  CHECK_DIF_OK(dif_lc_ctrl_configure(&lc, kDifLcCtrlStateDev, 0, &token),
               "LC transition configuration failed!");
  CHECK_DIF_OK(dif_lc_ctrl_transition(&lc), "LC transition failed!");

  // SV testbench waits for this message.
  LOG_INFO("LC transition requested.");
  wait_for_interrupt();
  return false;
}
