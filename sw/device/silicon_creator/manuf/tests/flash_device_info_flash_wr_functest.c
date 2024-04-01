// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "sw/device/silicon_creator/manuf/tests/test_wafer_auth_secret.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;

/**
 * Initializes all DIF handles used in this test.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR),
                       &lc_ctrl));
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());

  LOG_INFO("Executing from flash.");

  // Read LC state.
  dif_lc_ctrl_state_t lc_state = kDifLcCtrlStateInvalid;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));

  switch (lc_state) {
    case kDifLcCtrlStateProd:
    case kDifLcCtrlStateProdEnd:
      LOG_INFO("Reading the isolated flash partition.");
      uint32_t byte_address = 0;
      uint32_t
          actual_wafer_auth_secret[kFlashInfoWaferAuthSecretSizeIn32BitWords] =
              {0};
      CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
          &flash_ctrl_state, kFlashInfoFieldWaferAuthSecret.page,
          kFlashInfoFieldWaferAuthSecret.bank,
          kFlashInfoFieldWaferAuthSecret.partition, &byte_address));
      CHECK_STATUS_OK(flash_ctrl_testutils_read(
          &flash_ctrl_state, byte_address,
          kFlashInfoFieldWaferAuthSecret.partition, actual_wafer_auth_secret,
          kDifFlashCtrlPartitionTypeInfo,
          kFlashInfoWaferAuthSecretSizeIn32BitWords,
          /*delay_micros=*/0));
      CHECK_ARRAYS_EQ(actual_wafer_auth_secret, kExpectedWaferAuthSecret,
                      kFlashInfoWaferAuthSecretSizeIn32BitWords);
      LOG_INFO("Done.");
      break;
    default:
      LOG_ERROR("Unexpected LC state.");
      return false;
  }

  return true;
}
