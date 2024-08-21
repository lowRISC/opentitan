// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/rom/boot_policy_ptrs.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

static dif_flash_ctrl_state_t flash_ctrl;
static dif_rstmgr_t rstmgr;
static dif_otp_ctrl_t otp_ctrl;

static dif_flash_ctrl_region_properties_t kFlashFullAccessScrambledEcc = {
    .ecc_en = kMultiBitBool4True,
    .high_endurance_en = kMultiBitBool4False,
    .scramble_en = kMultiBitBool4True,
    .erase_en = kMultiBitBool4True,
    .prog_en = kMultiBitBool4True,
    .rd_en = kMultiBitBool4True};

/**
 * ROM_EXT slots.
 */
typedef enum rom_ext_slot {
  kRomExtSlotA = 0,
  kRomExtSlotB = 1,
} rom_ext_slot_t;

/**
 * Manifest offsets to corrupt.
 *
 * These fields are unique as they are read via pointer dereferces in the ROM.
 * See `sw/device/silicon_creator/lib/manifest.h`.
 */
enum {
  kManifestSecurityVersionOffset = 844,
  kManifestIdOffest = 820,
  kManifestLengthOffset = 832,
  kManifestManifestVersionOffset = 824,
  kManifestSignedRegionEndOffset = 828,
  kManifestCodeStartOffset = 892,
  kManifestCodeEndOffset = 896,
  kManifestEntryPointOffset = 900,
  kManifestEcdsaPublicKeyOffset = 432,
  kManifestUsageConstraintsSelectorBitsOffset = 384,
  kManifestEcdsaSignatureOffset = 0,
  kManifestExtensionsOffset = 904,
};

/**
 * ROM_EXT code offsets to corrupt.
 *
 * These are assigned non-word aligned values so thay can be differentiated from
 * the hardcoded manifest offsets above.
 */
enum {
  kCodeFirstWordOffset = 1,
  kCodeMiddleWordOffset = 2,
  kCodeLastWordOffset = 3,
};

enum {
  // First flash pages in each ROM_EXT slot.
  kRomExtSlotAFirstPageIndex = 0,
  kRomExtSlotBFirstPageIndex = FLASH_CTRL_PARAM_REG_PAGES_PER_BANK,

  // Addresses of the first words in each ROM_EXT slot.
  kRomExtSlotAFirstAddr = TOP_EARLGREY_EFLASH_BASE_ADDR,
  kRomExtSlotBFirstAddr =
      TOP_EARLGREY_EFLASH_BASE_ADDR + (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2),

  // Addresses of the manifest identifiers words in each ROM_EXT slot.
  kRomExtSlotAManifestIdAddr = kRomExtSlotAFirstAddr + kManifestIdOffest,
  kRomExtSlotBManifestIdAddr = kRomExtSlotBFirstAddr + kManifestIdOffest,

  // Flash banks for each half of flash.
  kFlashBank0DataRegion = 0,
  kFlashBank1DataRegion = 1,
};

OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, security_version,
                                kManifestSecurityVersionOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, identifier, kManifestIdOffest);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, length, kManifestLengthOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, manifest_version,
                                kManifestManifestVersionOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, signed_region_end,
                                kManifestSignedRegionEndOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, code_start,
                                kManifestCodeStartOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, code_end, kManifestCodeEndOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, entry_point,
                                kManifestEntryPointOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, ecdsa_public_key,
                                kManifestEcdsaPublicKeyOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, usage_constraints,
                                kManifestUsageConstraintsSelectorBitsOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, ecdsa_signature,
                                kManifestEcdsaSignatureOffset);
OT_ASSERT_MEMBER_OFFSET_AS_ENUM(manifest_t, extensions,
                                kManifestExtensionsOffset);

typedef struct corruption_word {
  /**
   * The byte offset within the flash bank to corrupt.
   */
  uint32_t offset;
  /**
   * A string description of what value is being corrupted.
   */
  char *description;
} corruption_word_t;

/**
 * Offsets of the manifest fields and code words we corrupt in this test.
 *
 * The fields of the manifest we corrupt are based on the order in which ROM
 * manifest fields are currently checked during boot process:
 *   1.  security_version
 *   2.  identifier
 *   3.  length
 *   4.  manifest_version->major
 *   5.  signed_region_end
 *   6.  code_start
 *   7.  code_end
 *   8.  entry_point
 *   9.  ecdsa public key
 *   10. spx+ public key (from manifest extension)
 *   11. spx+ signature (from manifest extension)
 *   12. usage_constraints->selector_bits,
 *   13. ecdsa signature
 *
 * We corrupt the flash ECC of each field / code word to test the ROM either:
 *   a. proceeds immediately to try to boot the next slot, or
 *   b. triggers a signature verification failure that will then cause the ROM
 *      to try to boot the next slot.
 */
static const corruption_word_t kWords2Corrupt[] = {
    // Manifest corruption offsets.
    {.offset = kManifestSecurityVersionOffset,
     .description = "manifest_security_version"},
    {.offset = kManifestIdOffest, .description = "manifest_identifier"},
    {.offset = kManifestLengthOffset, .description = "manifest_length"},
    {.offset = kManifestManifestVersionOffset,
     .description = "manifest_manifest_version"},
    {.offset = kManifestSignedRegionEndOffset,
     .description = "manifest_signed_region_end"},
    {.offset = kManifestCodeStartOffset, .description = "manifest_code_start"},
    {.offset = kManifestCodeEndOffset, .description = "manifest_code_end"},
    {.offset = kManifestEntryPointOffset,
     .description = "manifest_entry_point"},
    {.offset = kManifestEcdsaPublicKeyOffset,
     .description = "manifest_ecdsa_public_key"},
    {.offset = kManifestUsageConstraintsSelectorBitsOffset,
     .description = "manifest_usage_constraints_selector_bits"},
    {.offset = kManifestEcdsaSignatureOffset,
     .description = "manifest_ecdsa_signature"},
    {.offset = kManifestExtIdSpxKey,  // Represented as the extension ID; offset
                                      // is computed below.
     .description = "manifest_extension_spx_public_key"},
    {.offset = kManifestExtIdSpxSignature,  // Represented as the extension ID;
                                            // offset is computed below.
     .description = "manifest_extension_spx_signature"},

    // Code corruption offsets.
    {.offset = kCodeFirstWordOffset, .description = "code_first_word"},
};

static void init_peripherals(void) {
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
}

/**
 * Issue a software reset.
 */
static void sw_reset(void) {
  rstmgr_testutils_reason_clear();
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  wait_for_interrupt();
}

/**
 * Computes the page index of a byte address within a bank.
 */
static uint32_t compute_flash_page_index(rom_ext_slot_t rom_ext_slot,
                                         uint32_t byte_offset_in_bank) {
  uint32_t page_idx = rom_ext_slot == kRomExtSlotA ? kRomExtSlotAFirstPageIndex
                                                   : kRomExtSlotBFirstPageIndex;
  page_idx += byte_offset_in_bank / FLASH_CTRL_PARAM_BYTES_PER_PAGE;
  return page_idx;
}

/**
 * Corrupts a word of the currently running ROM_EXT at the provided offset
 * address of the given slot to trigger an ECC integrity errory (load access
 * fault) on the next boot.
 */
static status_t corrupt_rom_ext_word(rom_ext_slot_t slot,
                                     uint32_t offset_to_corrupt) {
  uint32_t page_idx = compute_flash_page_index(slot, offset_to_corrupt);
  uint32_t flash_data_bank =
      slot == kRomExtSlotA ? kFlashBank0DataRegion : kFlashBank1DataRegion;
  uint32_t first_flash_addr_in_slot =
      slot == kRomExtSlotA ? kRomExtSlotAFirstAddr : kRomExtSlotBFirstAddr;

  // Setup full access (read, erase, program) to first flash page in the slot.
  TRY(flash_ctrl_testutils_data_region_setup_properties(
      &flash_ctrl, page_idx, flash_data_bank,
      /*region_size=*/1, kFlashFullAccessScrambledEcc, NULL));

  // Read the flash word we are about to corrupt, via the flash_ctrl interface,
  // to confirm it is not corrupted.
  uint32_t word_to_corrupt = 0;
  TRY(flash_ctrl_testutils_read(
      &flash_ctrl, first_flash_addr_in_slot + offset_to_corrupt,
      /*partition_id=*/0, &word_to_corrupt, kDifFlashCtrlPartitionTypeData,
      /*word_count=*/1, /*delay_micros=*/0));
  LOG_INFO("Uncorrupted Flash Word: 0x%08x", word_to_corrupt);

  // Overwrite the target flash word inverted value (without first erasing the
  // page) to corrupt its ECC (since flash writes can only transition 1 bits to
  // 0 bits).
  uint32_t corrupted_word = ~word_to_corrupt;
  TRY(flash_ctrl_testutils_write(
      &flash_ctrl, first_flash_addr_in_slot + offset_to_corrupt,
      /*partition_id=*/0, &corrupted_word, kDifFlashCtrlPartitionTypeData,
      /*word_count=*/1));

  return OK_STATUS();
}

bool test_main(void) {
  init_peripherals();

  // Get the cause ID we will test and store the cause description in retention
  // SRAM (we will check it when the valid slot boots after a flash ECC error is
  // triggered).
  uint32_t cause_id = CAUSE_ID;  // Set in Bazel build file.
  CHECK(cause_id < ARRAYSIZE(kWords2Corrupt));
  char *corruption_desc = (char *)retention_sram_get()->owner.reserved;
  const char *str = kWords2Corrupt[cause_id].description;
  int len = -1;
  do {
    ++len;
    corruption_desc[len] = str[len];
  } while (str[len] != '\0' && len < sizeof(retention_sram_owner_t));

  // Get the manifest of the current slot we are running in.
  const manifest_t *manifest = manifest_def_get();

  // Compute the address we are corrupting within the slot. Some addresses are
  // hardcoded constants, others we must compute dynamically.
  uint32_t addr_of_corruption = kWords2Corrupt[cause_id].offset;
  switch (addr_of_corruption) {
    case kManifestExtIdSpxKey:
      CHECK(manifest->extensions.entries[0].identifier == kManifestExtIdSpxKey);
      addr_of_corruption = manifest->extensions.entries[0].offset;
      break;
    case kManifestExtIdSpxSignature:
      CHECK(manifest->extensions.entries[1].identifier ==
            kManifestExtIdSpxSignature);
      addr_of_corruption = manifest->extensions.entries[1].offset;
      break;
    case kCodeFirstWordOffset:
      addr_of_corruption = manifest->code_start;
      break;
    case kCodeMiddleWordOffset:
      addr_of_corruption =
          ((manifest->code_start + manifest->code_end) / 2) & ~0x3u;
      break;
    case kCodeLastWordOffset:
      addr_of_corruption = manifest->code_end;
      break;
    default:
      break;
  }

  // Corrupt the ECC of a targeted flash word by performing a double write.
  boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
  if (boot_log->rom_ext_slot == kBootSlotA) {
    LOG_INFO("Slot A self corrupting (%s) ...", corruption_desc);
    CHECK_STATUS_OK(corrupt_rom_ext_word(kRomExtSlotA, addr_of_corruption));
  } else {
    LOG_INFO("Slot B self corrupting (%s) ...", corruption_desc);
    CHECK_STATUS_OK(corrupt_rom_ext_word(kRomExtSlotB, addr_of_corruption));
  }

  // Issue a reset.
  LOG_INFO("Resetting chip to trigger load access fault in the ROM ...");
  sw_reset();

  return true;
}
