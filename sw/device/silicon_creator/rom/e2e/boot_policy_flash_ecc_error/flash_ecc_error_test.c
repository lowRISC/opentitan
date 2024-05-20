// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

#include "flash_ctrl_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

static dif_flash_ctrl_state_t flash_ctrl;
static dif_otp_ctrl_t otp_ctrl;

static dif_flash_ctrl_region_properties_t kFlashFullAccessScrambledEcc = {
    .ecc_en = kMultiBitBool4True,
    .high_endurance_en = kMultiBitBool4False,
    .scramble_en = kMultiBitBool4True,
    .erase_en = kMultiBitBool4True,
    .prog_en = kMultiBitBool4True,
    .rd_en = kMultiBitBool4True};

enum {
  // Manifest Offsets; See `sw/device/silicon_creator/lib/manifest.h`.
  kManifestIdOffest = 820,

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

void ottf_load_store_fault_handler(uint32_t *exc_info) {
  LOG_INFO("Load Access Fault ... continuing execution.");
  return;
}

static void init_peripherals(void) {
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp_ctrl));
}

static status_t corrupt_rom_ext_slot_a_identifier(void) {
  // Setup full access (read, erase, program) to first flash page in slot A.
  TRY(flash_ctrl_testutils_data_region_setup_properties(
      &flash_ctrl, kRomExtSlotAFirstPageIndex, kFlashBank0DataRegion,
      /*region_size=*/1, kFlashFullAccessScrambledEcc, NULL));

  // Read back the manifest identifier via the flash_ctrl and Ibex.
  uint32_t manifest_identifier = 0;
  TRY(flash_ctrl_testutils_read(&flash_ctrl, kRomExtSlotAManifestIdAddr,
                                /*partition_id=*/0, &manifest_identifier,
                                kDifFlashCtrlPartitionTypeData,
                                /*word_count=*/1, /*delay_micros=*/0));
  LOG_INFO("Uncorrupted Manifest ID (Flash Ctrl Read): 0x%08x",
           manifest_identifier);
  TRY_CHECK(manifest_identifier == CHIP_ROM_EXT_IDENTIFIER);
  // Read it back again via Ibex, expecting a load access fault.
  manifest_identifier = abs_mmio_read32(kRomExtSlotAManifestIdAddr);
  LOG_INFO("Uncorrupted Manifest ID (Ibex Read):      0x%08x",
           manifest_identifier);
  TRY_CHECK(manifest_identifier == CHIP_ROM_EXT_IDENTIFIER);

  // Overwrite the manifest_identifier with inverted value (without first
  // erasing the page) to corrupt ECC (since flash writes can only transition 1
  // bits to 0 bit).
  uint32_t inv_test_data = ~((uint32_t)CHIP_ROM_EXT_IDENTIFIER);
  TRY(flash_ctrl_testutils_write(&flash_ctrl, kRomExtSlotAManifestIdAddr,
                                 /*partition_id=*/0, &inv_test_data,
                                 kDifFlashCtrlPartitionTypeData,
                                 /*word_count=*/1));

  return OK_STATUS();
}

bool test_main(void) {
  init_peripherals();

  CHECK_STATUS_OK(corrupt_rom_ext_slot_a_identifier());

  // Read it back ROM_EXT slot A data via Ibex, expecting a load access fault.
  // TODO(timothytrippel): replace with chip reset to trigger slot B boot.
  uint32_t data_read = UINT32_MAX;
  data_read = abs_mmio_read32(kRomExtSlotAManifestIdAddr);
  LOG_INFO("Corrupted Data: 0x%08x", data_read);

  return true;
}
