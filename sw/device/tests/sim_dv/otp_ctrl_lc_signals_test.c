// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/otp_ctrl_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"

static dif_lc_ctrl_t lc;
static dif_otp_ctrl_t otp;
static dif_rstmgr_t rstmgr;
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_flash_ctrl_state_t flash;

// LC RMA token value in OTP SECRET2 partition.
static const uint8_t kOtpRmaToken[OTP_CTRL_PARAM_RMA_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

// Root key share 0 in OTP SECRET2 partition.
static const uint8_t
    kOtpRootKeyShare0[OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE] = {
        0x6e, 0x70, 0x48, 0x68, 0xa3, 0x2f, 0xfa, 0x1b, 0xd8, 0x36, 0x4d,
        0x00, 0x79, 0xbd, 0x04, 0xe6, 0x53, 0x18, 0xfc, 0xc3, 0xc9, 0xdd,
        0x39, 0xfa, 0xe0, 0x18, 0x49, 0x69, 0xc9, 0x81, 0x05, 0x17,
};

// Root key share 1 in OTP SECRET2 partition.
static const uint8_t
    kOtpRootKeyShare1[OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE] = {
        0x2f, 0x78, 0x6f, 0x93, 0x9a, 0xc4, 0xcf, 0x95, 0xb6, 0xec, 0x61,
        0x76, 0xbd, 0x08, 0x05, 0x0c, 0x09, 0x89, 0xe1, 0x73, 0x4b, 0x0a,
        0x59, 0x1b, 0xdd, 0x34, 0x84, 0x82, 0x32, 0x9a, 0x93, 0x31};

// Enum that encodes the possible test modes.
typedef enum { kWriteMode, kReadMode, kWriteReadMode } test_mode_t;

OTTF_DEFINE_TEST_CONFIG();

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  // Life cycle
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc));
  // OTP
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR), &otp));
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));
  // Rstmgr
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));
  // KMAC (init for Keymgr use)
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));
  CHECK_STATUS_OK(kmac_testutils_config(&kmac, true));
  // Keymgr
  CHECK_DIF_OK(dif_keymgr_init(
      mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR), &keymgr));
  // Flash
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash, mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
}

/**
 * Attempt to write the buffer to the specified address within the SECRET2
 * partition. If exp_result is set to kExpectFailed, the test expects the
 * access to fail with a DAI access error. If exp_result is set to
 * kExpectPassed, the test expects the test to pass without errors.
 */
static void otp_write_test(uint32_t address, const uint8_t *buffer,
                           uint32_t size, exp_test_result_t exp_result) {
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  for (uint32_t i = address; i < address + size; i += sizeof(uint64_t)) {
    uint64_t word;
    memcpy(&word, &buffer[i], sizeof(word));
    CHECK_DIF_OK(
        dif_otp_ctrl_dai_program64(&otp, kDifOtpCtrlPartitionSecret2, i, word));
    CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
    CHECK(address <= INT32_MAX, "address must fit into int32_t");
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_access_error_check(
        &otp, exp_result, (int32_t)address));
  }
}

/**
 * Attempt to read the OTP contents at the specified address within the SECRET2
 * partition, and compares the read data to the data in the buffer. If
 * exp_result is set to kExpectFailed, the test expects the access to fail
 * with a DAI access error, and it also expects the read data to NOT match with
 * the data in the buffer. If exp_result is set to kExpectPassed, the test
 * expects the test to pass without errors and the read data to match with the
 * data in the buffer.
 */
static void otp_read_test(uint32_t address, const uint8_t *buffer,
                          uint32_t size, exp_test_result_t exp_result) {
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  for (uint32_t i = address; i < address + size; i += sizeof(uint64_t)) {
    uint64_t got, exp;
    CHECK_DIF_OK(
        dif_otp_ctrl_dai_read_start(&otp, kDifOtpCtrlPartitionSecret2, i));
    CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
    CHECK(address <= INT32_MAX, "address must fit into int32_t");
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_access_error_check(
        &otp, exp_result, (int32_t)address));

    // Check whether the read data matches.
    memcpy(&exp, &buffer[i], sizeof(exp));
    CHECK_DIF_OK(dif_otp_ctrl_dai_read64_end(&otp, &got));
    if (exp_result == kExpectFailed) {
      CHECK(got != exp,
            "0x%x == 0x%x (got == exp) is not expected at address 0x%x", got,
            exp, address);
    } else {
      CHECK(got == exp,
            "0x%x != 0x%x (got != exp) is not expected at address 0x%x", got,
            exp, address);
    }
  }
}

/**
 * Test wrapper function that first calls the write and then the read test.
 */
static void otp_write_read_test(test_mode_t test_mode, uint32_t address,
                                const uint8_t *buffer, uint32_t size,
                                exp_test_result_t exp_result) {
  if (test_mode == kWriteMode || test_mode == kWriteReadMode) {
    LOG_INFO("Write test at 0x%x...", address);
    otp_write_test(address, buffer, size, exp_result);
  }
  if (test_mode == kReadMode || test_mode == kWriteReadMode) {
    LOG_INFO("Read test at 0x%x...", address);
    otp_read_test(address, buffer, size, exp_result);
  }
}

/**
 * Test wrapper function that calls the write and read tests above for all
 * objects within the SECRET2 partition.
 */
static void run_otp_access_tests(test_mode_t test_mode,
                                 exp_test_result_t exp_result) {
  otp_write_read_test(
      test_mode,
      OTP_CTRL_PARAM_RMA_TOKEN_OFFSET - OTP_CTRL_PARAM_SECRET2_OFFSET,
      (uint8_t *)kOtpRmaToken, OTP_CTRL_PARAM_RMA_TOKEN_SIZE, exp_result);
  otp_write_read_test(test_mode,
                      OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_OFFSET -
                          OTP_CTRL_PARAM_SECRET2_OFFSET,
                      (uint8_t *)kOtpRootKeyShare0,
                      OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE, exp_result);
  otp_write_read_test(test_mode,
                      OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_OFFSET -
                          OTP_CTRL_PARAM_SECRET2_OFFSET,
                      (uint8_t *)kOtpRootKeyShare1,
                      OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE, exp_result);
}

/**
 * Initialize and advance to kDifKeymgrStateCreatorRootKey state.
 */
static void keymgr_advance_to_creator_root_key(void) {
  // Check the last word of the retention SRAM creator area to determine the
  // type of the ROM.
  bool is_using_test_rom =
      retention_sram_get()
          ->creator
          .reserved[ARRAYSIZE((retention_sram_t){0}.creator.reserved) - 1] ==
      TEST_ROM_IDENTIFIER;
  CHECK_STATUS_OK(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateReset));
  CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, NULL));
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateInitialized));
  // Advance to kDifKeymgrStateCreatorRootKey state.
  if (is_using_test_rom) {
    LOG_INFO("Using test_rom, setting inputs and advancing state...");
    CHECK_DIF_OK(dif_keymgr_advance_state(&keymgr, &kCreatorParams));
  } else {
    LOG_INFO("Using rom, only advancing state...");
    CHECK_DIF_OK(dif_keymgr_advance_state_raw(&keymgr));
  }
}

/**
 * Checks that the first advance command does not complete.
 */
static void keymgr_check_cannot_advance(void) {
  LOG_INFO("Check that the Keymgr cannot advance...");
  CHECK_STATUS_OK(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateReset));
  // Try to initialize the key manager. We expect this call to fail with
  // a "kDifLocked" code, since the key manager is not enabled.
  CHECK(kDifLocked == dif_keymgr_advance_state(&keymgr, NULL),
        "Keymgr is not expected to be available in this LC state.");
}

/**
 * Check that the key manager flags the KMAC inputs as invalid. This happens
 * when the root keys are not valid and hence tied to all-zero inside the key
 * manager.
 */
static void keymgr_check_root_key_is_invalid(void) {
  dif_keymgr_status_codes_t status;
  keymgr_advance_to_creator_root_key();
  LOG_INFO("Check that the Keymgr root key is invalid...");
  do {
    CHECK_DIF_OK(dif_keymgr_get_status_codes(&keymgr, &status));
  } while (status == 0);
  CHECK(status ==
            (kDifKeymgrStatusCodeIdle | kDifKeymgrStatusCodeInvalidKmacInput),
        "Unexpected status: %x", status);
}

/**
 * Generate a SW key and store it within the retention SRAM.
 */
static void keymgr_check_can_generate_key(void) {
  keymgr_advance_to_creator_root_key();
  LOG_INFO("Check that the Keymgr can generate a key...");
  CHECK_STATUS_OK(keymgr_testutils_wait_for_operation_done(&keymgr));
  CHECK_STATUS_OK(
      keymgr_testutils_check_state(&keymgr, kDifKeymgrStateCreatorRootKey));
  CHECK_STATUS_OK(
      keymgr_testutils_generate_versioned_key(&keymgr, kKeyVersionedParams));
}

/**
 * Resets the chip.
 */
static void reset_chip(void) {
  CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
  busy_spin_micros(100);
  CHECK(false, "Should have reset before this line");
}

/**
 * This tests the impact of the lc_creator_seed_sw_rw_en and lc_seed_hw_rd_en
 * life cycle access control signals on the SECRET2 partition. Since it uses
 * the key manager to perform some of the testing, this test also checks the
 * impact of lc_keymgr_en on the key manager.
 *
 * The SECRETT2 partition should only be readable/writable by SW in
 * PROD/RMA/DEV. Once it is locked, the partition is not accessible by SW
 * anymore, but becomes accessible to HW (key manager).
 *
 * The test can be run in different life cycle states and figure out what to
 * check based on the state exposed in the life cycle controller.
 *
 * PROD/DEV/RMA:
 * 1)  Provision non-constant creator/owner secrets to flash
 * 2)  Program SECRET2 partition and read it back
 * 3)  Check that the key manager advance errors out due to all-zero root key
 * 4)  Reset the chip
 * 5)  Check that the SECRET2 partition can still be read
 * 6)  Check that the key manager advance errors out due to all-zero root key
 * 7)  Lock the SECRET2 partition
 * 8)  Reset the chip
 * 9)  Check that the SECRET2 partition is not accessible anymore
 * 10) Check that the key manager can generate a SW key without errors
 *
 * All other life cycle states:
 * 1) Check that key manager cannot be initialized because it is disabled
 * 2) Check the SECRET2 partition is not accessible
 *
 */
bool test_main(void) {
  bool is_computed;
  dif_lc_ctrl_state_t state;
  dif_rstmgr_reset_info_bitfield_t rst_info;
  init_peripherals();

  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc, &state));
  CHECK_STATUS_OK(lc_ctrl_testutils_lc_state_log(&state));

  switch (state) {
    case kDifLcCtrlStateDev:
    case kDifLcCtrlStateProd:
    case kDifLcCtrlStateProdEnd:
    case kDifLcCtrlStateRma:
      if (rst_info & kDifRstmgrResetInfoPor) {
        LOG_INFO("First access test iteration...");
        // Make sure the secrets in flash are non-zero.
        CHECK_STATUS_OK(keymgr_testutils_flash_init(&flash, &kCreatorSecret,
                                                    &kOwnerSecret));
        // Program the SECRET2 partition and perform read back test.
        run_otp_access_tests(kWriteReadMode, kExpectPassed);
        // We expect the root key to be invalid at this point.
        keymgr_check_root_key_is_invalid();
        reset_chip();

      } else if (rst_info == kDifRstmgrResetInfoSw) {
        CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
            &otp, kDifOtpCtrlPartitionSecret2, &is_computed));

        if (!is_computed) {
          LOG_INFO("Second access test iteration...");
          // SECRET2 partition should still be readable.
          run_otp_access_tests(kReadMode, kExpectPassed);
          // We expect the root key to still be invalid at this point, since
          // SECRET2 has not been locked yet.
          keymgr_check_root_key_is_invalid();
          // Lock the SECRET2 partition.
          CHECK_STATUS_OK(otp_ctrl_testutils_lock_partition(
              &otp, kDifOtpCtrlPartitionSecret2, 0));
          reset_chip();
        } else {
          LOG_INFO("Third access test iteration...");
          // All accesses are disallowed.
          run_otp_access_tests(kWriteReadMode, kExpectFailed);
          // At this point we expect that the key manager can generate keys
          // without errors.
          keymgr_check_can_generate_key();
          // Test passed.
          return true;
        }
      } else {
        LOG_ERROR("Unexpected reset info 0x%02X", rst_info);
      }

      break;
    default:  // this covers all TEST_UNLOCKED* states.
      // Accesses to the SECRET2 partition should error out.
      run_otp_access_tests(kWriteReadMode, kExpectFailed);
      // Keymgr initialization should not work in this state.
      keymgr_check_cannot_advance();
      // Test passed.
      return true;
  }

  return false;
}
