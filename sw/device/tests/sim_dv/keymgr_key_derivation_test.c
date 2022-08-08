// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"  // Generated.
#include "kmac_regs.h"    // Generated.

OTTF_DEFINE_TEST_CONFIG();

/** Place kmac into sideload mode for correct keymgr operation */
static void init_kmac_for_keymgr(void) {
  dif_kmac_t kmac;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .sideload = true,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));
}

bool test_main(void) {
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  // Initialize pwrmgr
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  info = rstmgr_testutils_reason_get();

  // POR reset
  if (info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");

    // Initialize flash
    keymgr_testutils_init_flash();

    // Lock otp secret partition
    dif_otp_ctrl_t otp;
    CHECK_DIF_OK(dif_otp_ctrl_init(
        mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
    otp_ctrl_testutils_lock_partition(&otp, kDifOtpCtrlPartitionSecret2, 0);

    // reboot device
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));

    // wait here until device reset
    wait_for_interrupt();

  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("Powered up for the second time, actuate keymgr");

    init_kmac_for_keymgr();

    dif_keymgr_t keymgr;
    CHECK_DIF_OK(dif_keymgr_init(
        mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));

    keymgr_testutils_check_state(&keymgr, kDifKeymgrStateReset);

    keymgr_testutils_advance_state(&keymgr, NULL);
    keymgr_testutils_check_state(&keymgr, kDifKeymgrStateInitialized);
    LOG_INFO("Keymgr entered Init State");

    keymgr_testutils_advance_state(&keymgr, &kCreatorParams);
    keymgr_testutils_check_state(&keymgr, kDifKeymgrStateCreatorRootKey);
    LOG_INFO("Keymgr entered CreatorRootKey State");

    keymgr_testutils_generate_identity(&keymgr);
    LOG_INFO("Keymgr generated identity at CreatorRootKey State");

    keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams);
    keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerIntermediateKey);
    LOG_INFO("Keymgr entered OwnerIntKey State");

    keymgr_testutils_generate_identity(&keymgr);
    LOG_INFO("Keymgr generated identity at OwnerIntKey State");

    keymgr_testutils_generate_versioned_key(&keymgr, kKeyVersionedParams);
    LOG_INFO("Keymgr generated SW output at OwnerIntKey State");

    // Generate sideload keys for 3 HW interfaces - Kmac, Aes, Otbn.
    dif_keymgr_versioned_key_params_t sideload_params = kKeyVersionedParams;
    sideload_params.dest = kDifKeymgrVersionedKeyDestKmac;
    keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
    LOG_INFO("Keymgr generated HW output for Kmac at OwnerIntKey State");

    sideload_params.dest = kDifKeymgrVersionedKeyDestAes;
    keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
    LOG_INFO("Keymgr generated HW output for Aes at OwnerIntKey State");

    sideload_params.dest = kDifKeymgrVersionedKeyDestOtbn;
    keymgr_testutils_generate_versioned_key(&keymgr, sideload_params);
    LOG_INFO("Keymgr generated HW output for Otbn at OwnerIntKey State");

    keymgr_testutils_disable(&keymgr);
    keymgr_testutils_check_state(&keymgr, kDifKeymgrStateDisabled);
    LOG_INFO("Keymgr entered Disabled state");

    return true;
  } else {
    LOG_FATAL("Unexpected reset reason unexpected: %0x", info);
  }

  return false;
}
