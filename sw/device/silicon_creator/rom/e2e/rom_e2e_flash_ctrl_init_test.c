// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

OTTF_DEFINE_TEST_CONFIG();

#define RUN_TEST(test_)                    \
  LOG_INFO("Starting test " #test_ "..."); \
  test_();                                 \
  LOG_INFO("Finished test " #test_ ": ok.");

enum {
  /**
   * Base address of the flash_ctrl registers.
   */
  kBase = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
};

typedef struct flash_cfg_reg {
  /**
   * Full register value.
   */
  uint32_t reg_value;
  /**
   * Bitfield for scrambling enable.
   */
  bitfield_field32_t scrambling_en;
  /**
   * Bitfield for ECC enable.
   */
  bitfield_field32_t ecc_en;
  /**
   * Bitfield for HE enable.
   */
  bitfield_field32_t he_en;
} flash_cfg_reg_t;

/**
 * Check that an info page is in the expected bank.
 */
static void check_info_page_bank(const flash_ctrl_info_page_t *info_page,
                                 uint32_t expected_bank) {
#define INFO_PAGE_BANK_CASE_(name_, bank_, page_) \
  if (&name_ == info_page) {                      \
    CHECK(bank_ == expected_bank);                \
    return;                                       \
  }

  FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_BANK_CASE_);
  CHECK(false);

#undef INFO_PAGE_BANK_CASE_
}

/**
 * Check that an info page has the expected page number.
 */
static void check_info_page_pagenum(const flash_ctrl_info_page_t *info_page,
                                    uint32_t expected_pagenum) {
#define INFO_PAGE_PAGENUM_CASE_(name_, bank_, page_) \
  if (&name_ == info_page) {                         \
    CHECK(page_ == expected_pagenum);                \
    return;                                          \
  }

  FLASH_CTRL_INFO_PAGES_DEFINE(INFO_PAGE_PAGENUM_CASE_);
  CHECK(false);

#undef INFO_PAGE_PAGENUM_CASE_
}

/**
 * Check that the configurations match.
 *
 * Compares the scrambling, ECC, and HE enable fields for equality and ensures
 * they are all valid multibit booleans.
 *
 * @param actual Actual configuration register.
 * @param expected Expected configuration register.
 */
static void check_cfg_match(flash_cfg_reg_t actual, flash_cfg_reg_t expected) {
  // Check that the values match.
  CHECK(bitfield_field32_read(actual.reg_value, actual.scrambling_en) ==
        bitfield_field32_read(expected.reg_value, expected.scrambling_en));
  CHECK(bitfield_field32_read(actual.reg_value, actual.ecc_en) ==
        bitfield_field32_read(expected.reg_value, expected.ecc_en));
  CHECK(bitfield_field32_read(actual.reg_value, actual.he_en) ==
        bitfield_field32_read(expected.reg_value, expected.he_en));
}

/**
 * Check that default data partition configurations match OTP.
 *
 * The `CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG` OTP value should match the
 * default scrambling, ecc, and he settings for the data partitions as
 * described in the `DEFAULT_REGION` flash controller register.
 */
static void default_cfg_test(void) {
  // Extract expected values from OTP.
  uint32_t otp_default_cfg_value =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET);
  flash_cfg_reg_t otp_default_cfg = {
      .reg_value = otp_default_cfg_value,
      .scrambling_en = FLASH_CTRL_OTP_FIELD_SCRAMBLING,
      .ecc_en = FLASH_CTRL_OTP_FIELD_ECC,
      .he_en = FLASH_CTRL_OTP_FIELD_HE,
  };

  // Read actual values from the flash controller.
  uint32_t default_cfg_value =
      abs_mmio_read32(kBase + FLASH_CTRL_DEFAULT_REGION_REG_OFFSET);
  flash_cfg_reg_t default_cfg = {
      .reg_value = default_cfg_value,
      .scrambling_en = FLASH_CTRL_DEFAULT_REGION_SCRAMBLE_EN_FIELD,
      .ecc_en = FLASH_CTRL_DEFAULT_REGION_ECC_EN_FIELD,
      .he_en = FLASH_CTRL_DEFAULT_REGION_HE_EN_FIELD,
  };

  // Check that the two match.
  check_cfg_match(default_cfg, otp_default_cfg);
}

/**
 * Check that boot partition info pages match OTP.
 *
 * The `CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG` OTP value should match the
 * scrambling, ecc, and he settings in info0 for the boot partitions
 * `kFlashCtrlInfoPageBootData0` (bank 1, page 0) and
 * `kFlashCtrlInfoPageBootData1` (bank 1, page 1).
 */
static void boot_info_cfg_test(void) {
  // Double-check the expected bank and page number for the boot info pages.
  // These numbers are hardcoded below to mitigate risk from errors in macros
  // that construct the page-specific constants.
  //
  // Expected values:
  // * kFlashCtrlInfoPageBootData0 -> bank 1, page 0
  // * kFlashCtrlInfoPageBootData1 -> bank 1, page 1
  check_info_page_bank(&kFlashCtrlInfoPageBootData0, 1);
  check_info_page_pagenum(&kFlashCtrlInfoPageBootData0, 0);
  check_info_page_bank(&kFlashCtrlInfoPageBootData1, 1);
  check_info_page_pagenum(&kFlashCtrlInfoPageBootData1, 1);

  // Extract expected values from OTP.
  uint32_t otp_boot_info_cfg_value =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_INFO_BOOT_DATA_CFG_OFFSET);
  flash_cfg_reg_t otp_boot_info_cfg = {
      .reg_value = otp_boot_info_cfg_value,
      .scrambling_en = FLASH_CTRL_OTP_FIELD_SCRAMBLING,
      .ecc_en = FLASH_CTRL_OTP_FIELD_ECC,
      .he_en = FLASH_CTRL_OTP_FIELD_HE,
  };

  // Check the configuration for bank 1, page 0.
  uint32_t page0_cfg_value =
      abs_mmio_read32(kBase + FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_REG_OFFSET);
  flash_cfg_reg_t page0_cfg = {
      .reg_value = page0_cfg_value,
      .scrambling_en = FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_SCRAMBLE_EN_0_FIELD,
      .ecc_en = FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_ECC_EN_0_FIELD,
      .he_en = FLASH_CTRL_BANK1_INFO0_PAGE_CFG_0_HE_EN_0_FIELD,
  };
  check_cfg_match(page0_cfg, otp_boot_info_cfg);

  // Check the configuration for bank 1, page 1.
  uint32_t page1_cfg_value =
      abs_mmio_read32(kBase + FLASH_CTRL_BANK1_INFO0_PAGE_CFG_1_REG_OFFSET);
  flash_cfg_reg_t page1_cfg = {
      .reg_value = page1_cfg_value,
      .scrambling_en = FLASH_CTRL_BANK1_INFO0_PAGE_CFG_1_SCRAMBLE_EN_1_FIELD,
      .ecc_en = FLASH_CTRL_BANK1_INFO0_PAGE_CFG_1_ECC_EN_1_FIELD,
      .he_en = FLASH_CTRL_BANK1_INFO0_PAGE_CFG_1_HE_EN_1_FIELD,
  };
  check_cfg_match(page1_cfg, otp_boot_info_cfg);
}

/**
 * Verify that the flash controller is initialized.
 */
static void is_initialized_test(void) {
  // Check that the `INIT` register is nonzero, indicating that the flash
  // controller received the signal to initialize on startup.
  uint32_t init = abs_mmio_read32(kBase + FLASH_CTRL_INIT_REG_OFFSET);
  CHECK(bitfield_bit32_read(init, FLASH_CTRL_INIT_VAL_BIT) == true);

  // Check that the physical status register does not say flash controller is
  // still initializing.
  uint32_t phy_status =
      abs_mmio_read32(kBase + FLASH_CTRL_PHY_STATUS_REG_OFFSET);
  CHECK(bitfield_bit32_read(phy_status, FLASH_CTRL_PHY_STATUS_INIT_WIP_BIT) ==
        false);

  // Check that the general status register does not say flash controller is
  // still initializing, and that the FIFOs are empty.
  uint32_t status = abs_mmio_read32(kBase + FLASH_CTRL_STATUS_REG_OFFSET);
  CHECK(bitfield_bit32_read(status, FLASH_CTRL_STATUS_INIT_WIP_BIT) == false);
  CHECK(bitfield_bit32_read(status, FLASH_CTRL_STATUS_RD_EMPTY_BIT) == true);
  CHECK(bitfield_bit32_read(status, FLASH_CTRL_STATUS_PROG_EMPTY_BIT) == true);
}

bool test_main(void) {
  RUN_TEST(default_cfg_test);
  RUN_TEST(boot_info_cfg_test);
  RUN_TEST(is_initialized_test);
  return true;
}
