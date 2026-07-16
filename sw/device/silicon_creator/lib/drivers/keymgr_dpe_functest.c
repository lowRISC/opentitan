// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/keymgr_dpe_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr_dpe.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_dpe_binding_value.h"

#include "hw/top/keymgr_dpe_regs.h"
#include "hw/top/kmac_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
 * Software binding value associated with the ROM. Programmed by the ROM.
 */
keymgr_dpe_binding_value_t kBindingValueRom = {
    .data = {0x7c9b2405, 0x1841a738, 0xdb24005d, 0x4dbd6a17, 0x362f1673,
             0x1d8ede70, 0x0104d346, 0x1a0806c2},
};

/**
 * Software binding value associated with the ROM_EXT. Programmed by ROM.
 */
keymgr_dpe_binding_value_t kBindingValueRomExt = {
    .data = {0xdc96c23d, 0xaf36e268, 0xcb68ff71, 0xe92f76e2, 0xb8a8379d,
             0x426dc745, 0x19f5cff7, 0x4ec9c6d6},
};

/**
 * Software binding value associated with BL0. Programmed by ROM_EXT.
 */
keymgr_dpe_binding_value_t kBindingValueBl0Attestation = {
    .data = {0xe4987b39, 0x3f83d390, 0xc2f3bbaf, 0x3195dbfa, 0x23fb480c,
             0xb012ae5e, 0xf1394d28, 0x1940ceeb},
};
keymgr_dpe_binding_value_t kBindingValueBl0Sealing = {
    .data = {0x195ef742, 0xab3063c1, 0x98411a23, 0x1fa03b22, 0xc0931e65,
             0xd3068ee2, 0x2950bf31, 0x749e21a3},
};

/**
 * Default DPE context policy
 */
const sc_keymgr_dpe_policies_t kDefaultPolicy = {
    .child = kScKeymgrDPESlotPolAllowChild,
    .parent = kScKeymgrDPESlotPolEraseParent,
    .expo = kScKeymgrDPESlotPolNoExport,
};

/**
 * Kmac prefix "KMAC" with empty custom string
 */
const uint32_t kKmacPrefix[kKmacPrefixSize] = {
    0x4d4b2001, 0x00014341, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
};

/** ROM key manager maximum version. */
const uint32_t kMaxVerRom = 1;

/** ROM_EXT key manager maximum version. */
const uint32_t kMaxVerRomExt = 2;

/** BL0 key manager maximum version. */
const uint32_t kMaxVerBl0 = 3;

/** Pre defined slots for each secret. */
const uint32_t seal_slot = 0;
const uint32_t att_slot = 1;

OTTF_DEFINE_TEST_CONFIG();

static void init_flash(void) {
  dif_flash_ctrl_state_t flash;

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize flash secrets.
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_flash_init(&flash, &kCreatorSecret, &kOwnerSecret));
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
rom_error_t keymgr_dpe_rom_test(void) {
  // Bypass the CreatorRootKey when not in TEST_ROM as the key should already be
  // derived by the rom code.
  if (retention_sram_get()
          ->creator
          .reserved[ARRAYSIZE((retention_sram_t){0}.creator.reserved) - 1] ==
      TEST_ROM_IDENTIFIER) {
    // Bring the keymgr dpe out of the reset state and load the UDS.
    // After this operation the keymgr dpe is in the Available state.
    ASSERT_OK(sc_keymgr_dpe_advance_initial(seal_slot));
    LOG_INFO("Keymgr DPE: UDS loaded");

    // Set the reseeding interval
    const uint16_t kEntropyReseedInterval = 0x1234;
    sc_keymgr_dpe_entropy_reseed_interval_set(kEntropyReseedInterval);
    SEC_MMIO_WRITE_INCREMENT(kScKeymgrDPESecMmioReseedIntervalSet);
    sec_mmio_check_values(/*rnd_offset=*/0);

    // ------ CreatorRootKey Stage ------------------------
    // Derive both the attestation and sealing CreatorRootKey
    sc_keymgr_dpe_advance_data_t attestation_key = {
        .binding_value = &kBindingValueRom,
        .policy = kDefaultPolicy,
        .sel_src_slot = att_slot,
        .sel_dst_slot = att_slot,
        .version = kMaxVerRom};
    sc_keymgr_dpe_advance_data_t sealing_key = {
        .binding_value = &kBindingValueRom,
        .policy = kDefaultPolicy,
        .sel_src_slot = seal_slot,
        .sel_dst_slot = seal_slot,
        .version = kMaxVerRom};

    SEC_MMIO_WRITE_INCREMENT(
        2 * (kScKeymgrDPESecMmioSwBindingSet + kScKeymgrDPESecMmioMaxVerSet));
    SEC_MMIO_WRITE_INCREMENT(2 * (kScKeymgrDPESecMmioSlotPolicy));

    ASSERT_OK(sc_keymgr_dpe_advance_creator(sealing_key, attestation_key));
    LOG_INFO("Keymgr DPE: CreatorRootKey derived");
    sec_mmio_check_values(/*rnd_offset=*/0);

    // ------ OwnerIntKey Stage ------------------------
    // Derive both the attestation and sealing OwnerIntKey
    attestation_key.binding_value = &kBindingValueRomExt;
    attestation_key.version = kMaxVerRomExt;
    sealing_key.binding_value = &kBindingValueRomExt;
    sealing_key.version = kMaxVerRomExt;

    SEC_MMIO_WRITE_INCREMENT(
        2 * (kScKeymgrDPESecMmioSwBindingSet + kScKeymgrDPESecMmioMaxVerSet));
    SEC_MMIO_WRITE_INCREMENT(2 * (kScKeymgrDPESecMmioSlotPolicy));

    ASSERT_OK(sc_keymgr_dpe_advance_owner_int(sealing_key, attestation_key));
    LOG_INFO("Keymgr DPE: OwnerIntKey derived");
    sec_mmio_check_values(/*rnd_offset=*/0);

    sec_mmio_check_counters(/*expected_check_count=*/3);
  }
  return kErrorOk;
}

/** Key manager configuration steps performed in ROM_EXT. */
rom_error_t keymgr_dpe_rom_ext_test(void) {
  // ------ OwnerKey Stage ------------------------
  // Derive both the attestation and sealing OwnerKey
  sc_keymgr_dpe_advance_data_t attestation_key = {
      .binding_value = &kBindingValueBl0Attestation,
      .policy = kDefaultPolicy,
      .sel_src_slot = att_slot,
      .sel_dst_slot = att_slot,
      .version = kMaxVerBl0};
  sc_keymgr_dpe_advance_data_t sealing_key = {
      .binding_value = &kBindingValueBl0Sealing,
      .policy = kDefaultPolicy,
      .sel_src_slot = seal_slot,
      .sel_dst_slot = seal_slot,
      .version = kMaxVerBl0};

  SEC_MMIO_WRITE_INCREMENT(
      2 * (kScKeymgrDPESecMmioSwBindingSet + kScKeymgrDPESecMmioMaxVerSet));
  SEC_MMIO_WRITE_INCREMENT(2 * (kScKeymgrDPESecMmioSlotPolicy));

  ASSERT_OK(sc_keymgr_dpe_advance_owner(sealing_key, attestation_key));
  LOG_INFO("Keymgr DPE: OwnerKey derived");
  sec_mmio_check_values(/*rnd_offset=*/0);

  sec_mmio_check_counters(/*expected_check_count=*/5);

  return kErrorOk;
}

rom_error_t keymgr_dpe_generate_sw_keys(void) {
  // Generate a key from each the sealing and attestation DPE context
  // Compare the keys, the must be different as different binding values
  // are used.
  sc_keymgr_dpe_diversification_t key_data = {
      .salt = {0x0, 0x1, 0x2, 0x3, 0x80, 0x81, 0x82, 0x83},
      .sel_src_slot = seal_slot,
      .version = 0,
  };

  uint32_t attestation_derived_key[2][kScKeymgrDPEKeyNumWords] = {0};
  uint32_t sealing_derived_key[2][kScKeymgrDPEKeyNumWords] = {0};

  // Generate the key from the sealing context
  ASSERT_OK(sc_keymgr_dpe_generate_key(kScKeymgrDPEDestNone, key_data));
  ASSERT_OK(sc_keymgr_dpe_read_key(attestation_derived_key[0],
                                   attestation_derived_key[1]));

  // Generate the key from the attestation context
  key_data.sel_src_slot = att_slot;
  ASSERT_OK(sc_keymgr_dpe_generate_key(kScKeymgrDPEDestNone, key_data));
  ASSERT_OK(
      sc_keymgr_dpe_read_key(sealing_derived_key[0], sealing_derived_key[1]));

  // Combine shares and check if the two keys are not equal
  bool matching_key = true;
  for (int idx = 0; idx < kScKeymgrDPEKeyNumWords; idx++) {
    if ((attestation_derived_key[0][idx] ^ attestation_derived_key[1][idx]) !=
        (sealing_derived_key[0][idx] ^ sealing_derived_key[1][idx])) {
      matching_key = false;
      break;
    }
  }
  CHECK(!matching_key,
        "KeymgrDpe generated two matching key for the attestation and sealing "
        "DPE context");

  return kErrorOk;
}

rom_error_t keymgr_dpe_disable_test(void) {
  sc_keymgr_dpe_disable();
  CHECK(sc_keymgr_dpe_state_check(kScKeymgrDPEStateDisabled) == kErrorOk,
        "Keymgr should be in the disabled state.");
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();
  dif_rstmgr_t rstmgr;
  dif_rstmgr_reset_info_bitfield_t info;

  lifecycle_state_t lc_state = lifecycle_state_get();
  CHECK(lc_state == kLcStateRma || lc_state == kLcStateDev ||
            lc_state == kLcStateProd || lc_state == kLcStateProdEnd,
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
    kmac_keymgr_configure();

    EXECUTE_TEST(result, keymgr_dpe_rom_test);
    EXECUTE_TEST(result, keymgr_dpe_rom_ext_test);
    EXECUTE_TEST(result, keymgr_dpe_generate_sw_keys);
    EXECUTE_TEST(result, keymgr_dpe_disable_test);
    return status_ok(result);
  } else {
    LOG_FATAL("Unexpected reset reason unexpected: %08x", info);
  }

  return false;
}
