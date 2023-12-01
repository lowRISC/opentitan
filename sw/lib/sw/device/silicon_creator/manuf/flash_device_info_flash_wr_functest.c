// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/flash_ctrl/dif/dif_flash_ctrl.h"
#include "sw/ip/flash_ctrl/driver/flash_ctrl.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/lc_ctrl/driver/lc_ctrl.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/silicon_creator/manuf/isolated_flash_partition.h"
#include "sw/lib/sw/device/silicon_creator/manuf/test_wafer_auth_secret.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_flash_ctrl_state_t flash_ctrl_state;
static dif_lc_ctrl_t lc_ctrl;

/**
 * Initializes all DIF handles used in this test.
 */
static status_t peripheral_handles_init(void) {
  TRY(dif_flash_ctrl_init_state(
      &flash_ctrl_state, mmio_region_from_addr(kFlashCtrlCoreBaseAddr[0])));
  TRY(dif_lc_ctrl_init(mmio_region_from_addr(kLcCtrlRegsBaseAddr[0]),
                       &lc_ctrl));
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());

  LOG_INFO("Executing from flash.");

  // Read LC state.
  dif_lc_ctrl_state_t lc_state = kDifLcCtrlStateInvalid;
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));

  uint32_t actual_wafer_auth_secret[kWaferAuthSecretSizeInWords] = {0};

  switch (lc_state) {
    case kDifLcCtrlStateProd:
    case kDifLcCtrlStateProdEnd:
      LOG_INFO("Reading the isolated flash partition.");
      CHECK_STATUS_OK(isolated_flash_partition_read(&flash_ctrl_state,
                                                    kWaferAuthSecretSizeInWords,
                                                    actual_wafer_auth_secret));
      CHECK_ARRAYS_EQ(actual_wafer_auth_secret, kExpectedWaferAuthSecret,
                      kWaferAuthSecretSizeInWords);
      LOG_INFO("Done.");
      break;
    default:
      LOG_ERROR("Unexpected LC state.");
      return false;
  }

  return true;
}
