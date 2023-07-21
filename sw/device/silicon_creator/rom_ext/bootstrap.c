// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/bootstrap.h"

#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/bootstrap.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "flash_ctrl_regs.h"
#include "hw/ip/otp_ctrl/data/otp_ctrl_regs.h"

enum {
  /*
   * Maximum flash address, exclusive.
   */
  kMaxAddress =
      FLASH_CTRL_PARAM_BYTES_PER_BANK * FLASH_CTRL_PARAM_REG_NUM_BANKS,
  /*
   * The total number of flash pages.
   */
  kNumPages =
      FLASH_CTRL_PARAM_REG_PAGES_PER_BANK * FLASH_CTRL_PARAM_REG_NUM_BANKS,

};

rom_error_t bootstrap_chip_erase(void) {
  // Unlike ROM bootstrap, we cannot erase entire banks at a time because that
  // would erase ROM_EXT regions as well.
  flash_ctrl_bank_erase_perms_set(kHardenedBoolTrue);
  rom_error_t last_err = kErrorOk;
  for (uint32_t i = 0; i < kNumPages; ++i) {
    const uint32_t addr = i * FLASH_CTRL_PARAM_BYTES_PER_PAGE;
    // Do not erase this page if it lies within ROM_EXT on either slot.
    if (addr < CHIP_ROM_EXT_SIZE_MAX ||
        (addr >= FLASH_CTRL_PARAM_BYTES_PER_BANK &&
         addr < FLASH_CTRL_PARAM_BYTES_PER_BANK + CHIP_ROM_EXT_SIZE_MAX)) {
      continue;
    }
    rom_error_t err = flash_ctrl_data_erase(addr, kFlashCtrlEraseTypePage);
    if (err != kErrorOk) {
      last_err = err;
    }
  }
  flash_ctrl_bank_erase_perms_set(kHardenedBoolFalse);
  return last_err;
}

rom_error_t bootstrap_erase_verify(void) {
  rom_error_t last_err = kErrorOk;
  for (uint32_t i = 0; i < kNumPages; ++i) {
    const uint32_t addr = i * FLASH_CTRL_PARAM_BYTES_PER_PAGE;
    // Do not verify this page if it lies within ROM_EXT on either slot.
    if (addr < CHIP_ROM_EXT_SIZE_MAX ||
        (addr >= FLASH_CTRL_PARAM_BYTES_PER_BANK &&
         addr < FLASH_CTRL_PARAM_BYTES_PER_BANK + CHIP_ROM_EXT_SIZE_MAX)) {
      continue;
    }
    rom_error_t err =
        flash_ctrl_data_erase_verify(addr, kFlashCtrlEraseTypePage);
    if (err != kErrorOk) {
      last_err = err;
    }
  }
  return last_err;
}

hardened_bool_t rom_ext_bootstrap_enabled(void) {
  // Check that bootstrap is enabled in OTP.
  uint32_t bootstrap_en =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN_OFFSET);
  if (launder32(bootstrap_en) != kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(bootstrap_en, kHardenedBoolTrue);

  // Check that the reset reason is PoR.
  const uint32_t reset_mask = 1 << kRstmgrReasonPowerOn;
  const uint32_t reset_reason = rstmgr_reason_get();
  const uint32_t is_por = reset_reason & reset_mask;
  if (launder32(is_por) == 0) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_EQ(is_por, reset_mask);
  return kHardenedBoolTrue;
}

rom_error_t rom_ext_bootstrap(void) {
  hardened_bool_t enabled = rom_ext_bootstrap_enabled();
  if (launder32(enabled) != kHardenedBoolTrue) {
    return kErrorBootstrapDisabledRomExt;
  }
  HARDENED_CHECK_EQ(enabled, kHardenedBoolTrue);

  enum {
    kNumPagesInRomExt = CHIP_ROM_EXT_SIZE_MAX / FLASH_CTRL_PARAM_BYTES_PER_PAGE
  };
  static_assert(CHIP_ROM_EXT_SIZE_MAX % FLASH_CTRL_PARAM_BYTES_PER_PAGE == 0,
                "ROM_EXT size must be an integer multiple of flash page size.");
  static_assert(kNumPagesInRomExt <= FLASH_CTRL_PARAM_REG_PAGES_PER_BANK,
                "ROM_EXT must fit within a single flash bank.");

  // Read the DEFAULT_REGION register to determine default values for some
  // fields of MP_REGION_CFG_${region}.
  const flash_ctrl_cfg_t default_cfg = flash_ctrl_data_default_cfg_get();

  // The region of slot A following the ROM_EXT region is erasable and
  // programmable.
  flash_ctrl_data_region_protect(
      /*region=*/0,
      /*page_offset=*/kNumPagesInRomExt,
      /*num_pages=*/FLASH_CTRL_PARAM_REG_PAGES_PER_BANK - kNumPagesInRomExt,
      (flash_ctrl_perms_t){
          .read = kMultiBitBool4True,
          .write = kMultiBitBool4True,
          .erase = kMultiBitBool4True,
      },
      default_cfg);

  // The region of slot B following the ROM_EXT region is erasable, but not
  // programmable.
  flash_ctrl_data_region_protect(
      /*region=*/1,
      /*page_offset=*/FLASH_CTRL_PARAM_REG_PAGES_PER_BANK + kNumPagesInRomExt,
      /*num_pages=*/FLASH_CTRL_PARAM_REG_PAGES_PER_BANK - kNumPagesInRomExt,
      (flash_ctrl_perms_t){
          .read = kMultiBitBool4True,
          .write = kMultiBitBool4False,
          .erase = kMultiBitBool4True,
      },
      default_cfg);

  // With the lowest priority, disable programming and erasing the flash.
  flash_ctrl_data_region_protect(
      /*region=*/2,
      /*page_offset=*/0,
      /*num_pages=*/FLASH_CTRL_PARAM_REG_PAGES_PER_BANK *
          FLASH_CTRL_PARAM_REG_NUM_BANKS,
      (flash_ctrl_perms_t){
          .read = kMultiBitBool4True,
          .write = kMultiBitBool4False,
          .erase = kMultiBitBool4False,
      },
      default_cfg);

  return enter_bootstrap();
}
