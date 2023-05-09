// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"
#include "kmac_regs.h"

#define ASSERT_OK(expr_)                        \
  do {                                          \
    rom_error_t local_error_ = expr_;           \
    if (local_error_ != kErrorOk) {             \
      LOG_ERROR("Error at line: %d", __LINE__); \
      return local_error_;                      \
    }                                           \
  } while (0)

#define ASSERT_EQZ(x) CHECK((x) == 0)

enum {
  /** Flash Secret partition ID. */
  kFlashInfoPartitionId = 0,

  /** Secret partition flash bank ID. */
  kFlashInfoBankId = 0,

  /** Creator Secret flash info page ID. */
  kFlashInfoPageIdCreatorSecret = 1,

  /** Owner Secret flash info page ID. */
  kFlashInfoPageIdOwnerSecret = 2,

  /** Key manager secret word size. */
  kSecretWordSize = 16,

  /** KMAC prefix word size. */
  kKmacPrefixSize = 11,
};

/**
 * Software binding value associated with the ROM_EXT. Programmed by
 * ROM.
 */
const keymgr_binding_value_t kBindingValueRomExt = {
    .data = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2, 0xb8a8379d,
             0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
};

/**
 * Software binding value associated with BL0. Programmed by ROM_EXT.
 */
const keymgr_binding_value_t kBindingValueBl0 = {
    .data = {0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa, 0x23fb480c,
             0xb012ae5e, 0xf1394d28, 0x1940ceeb},
};

/**
 * Kmac prefix "KMAC" with empty custom string
 */
const uint32_t kKmacPrefix[kKmacPrefixSize] = {
    0x4d4b2001, 0x00014341, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
};

/** ROM_EXT key manager maximum version. */
const uint32_t kMaxVerRomExt = 1;

/** BL0 key manager maximum version. */
const uint32_t kMaxVerBl0 = 2;

OTTF_DEFINE_TEST_CONFIG();

static void init_flash(void) {
  dif_flash_ctrl_state_t flash;

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize flash secrets.
  CHECK_STATUS_OK(
      keymgr_testutils_flash_init(&flash, &kCreatorSecret, &kOwnerSecret));
}

/** Place kmac into sideload mode for correct keymgr operation */
static void init_kmac_for_keymgr(void) {
  dif_kmac_t kmac;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_fast_process = false,
      .entropy_seed = {0xaa25b4bf, 0x48ce8fff, 0x5a78282a, 0x48465647,
                       0x70410fef},
      .sideload = true,
      .msg_mask = true,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));
}

static void check_lock_otp_partition(const dif_otp_ctrl_t *otp) {
  bool is_computed;
  CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(otp, kDifOtpCtrlPartitionSecret2,
                                               &is_computed));
  if (is_computed) {
    uint64_t digest;
    CHECK_DIF_OK(
        dif_otp_ctrl_get_digest(otp, kDifOtpCtrlPartitionSecret2, &digest));
    LOG_INFO("OTP partition locked. Digest: %x-%x", ((uint32_t *)&digest)[0],
             ((uint32_t *)&digest)[1]);
    return;
  }
  CHECK_STATUS_OK(
      otp_ctrl_testutils_lock_partition(otp, kDifOtpCtrlPartitionSecret2, 0));
}

/** Key manager configuration steps performed in ROM. */
rom_error_t keymgr_rom_test(void) {
  ASSERT_OK(keymgr_state_check(kKeymgrStateReset));
  if (retention_sram_get()
          ->reserved_creator[ARRAYSIZE((retention_sram_t){0}.reserved_creator) -
                             1] == TEST_ROM_IDENTIFIER) {
    keymgr_sw_binding_set(&kBindingValueRomExt, &kBindingValueRomExt);
    keymgr_creator_max_ver_set(kMaxVerRomExt);
    SEC_MMIO_WRITE_INCREMENT(kKeymgrSecMmioSwBindingSet +
                             kKeymgrSecMmioCreatorMaxVerSet);
  }
  sec_mmio_check_values(/*rnd_offset=*/0);
  sec_mmio_check_counters(/*expected_check_count=*/1);
  return kErrorOk;
}

/** Key manager configuration steps performed in ROM_EXT. */
rom_error_t keymgr_rom_ext_test(void) {
  const uint16_t kEntropyReseedInterval = 0x1234;
  ASSERT_OK(keymgr_init(kEntropyReseedInterval));
  SEC_MMIO_WRITE_INCREMENT(kKeymgrSecMmioInit);
  sec_mmio_check_values(/*rnd_offset=*/0);

  keymgr_advance_state();
  ASSERT_OK(keymgr_state_check(kKeymgrStateInit));
  LOG_INFO("Keymgr State: Init");

  keymgr_advance_state();
  ASSERT_OK(keymgr_state_check(kKeymgrStateCreatorRootKey));

  // The software binding register lock is reset after advancing the key
  // manager, so we need to call this function to update sec_mmio expectation
  // table.
  keymgr_sw_binding_unlock_wait();
  sec_mmio_check_values(/*rnd_offset=*/0);

  keymgr_sw_binding_set(&kBindingValueBl0, &kBindingValueBl0);
  keymgr_owner_int_max_ver_set(kMaxVerBl0);
  SEC_MMIO_WRITE_INCREMENT(kKeymgrSecMmioSwBindingSet +
                           kKeymgrSecMmioOwnerIntMaxVerSet);
  sec_mmio_check_values(/*rnd_offset=*/0);

  keymgr_advance_state();
  ASSERT_OK(keymgr_state_check(kKeymgrStateOwnerIntermediateKey));

  sec_mmio_check_counters(/*expected_check_count=*/5);
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  CHECK(lifecycle_state_get() == kLcStateRma,
        "The test is configured to run in RMA mode.");

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  info = rstmgr_testutils_reason_get();

  dif_otp_ctrl_t otp;
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));

  if (info & kDifRstmgrResetInfoPor) {
    LOG_INFO("Powered up for the first time, program flash");
    init_flash();

    // This is done after `init_flash()` because in DEV and PROD stages the
    // info flash secret partition becomes unavailable.
    check_lock_otp_partition(&otp);

    // Issue and wait for reset.
    rstmgr_testutils_reason_clear();
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    wait_for_interrupt();
  } else if (info == kDifRstmgrResetInfoSw) {
    LOG_INFO("Powered up for the second time, actuate keymgr");

    check_lock_otp_partition(&otp);
    sec_mmio_init();
    init_kmac_for_keymgr();

    EXECUTE_TEST(result, keymgr_rom_test);
    EXECUTE_TEST(result, keymgr_rom_ext_test);
    return status_ok(result);
  } else {
    LOG_FATAL("Unexpected reset reason unexpected: %08x", info);
  }

  return false;
}
