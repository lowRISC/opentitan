// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/ip/keymgr_dpe/test/utils/keymgr_dpe_testutils.h"
#include "sw/ip/kmac/dif/dif_kmac.h"
#include "sw/ip/kmac/test/utils/kmac_testutils.h"
#include "sw/ip/lc_ctrl/dif/dif_lc_ctrl.h"
#include "sw/ip/lc_ctrl/test/utils/lc_ctrl_testutils.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/otp_ctrl/test/utils/otp_ctrl_testutils.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rstmgr/test/utils/rstmgr_testutils.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/silicon_creator/base/chip.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"

static dif_lc_ctrl_t lc;
static dif_otp_ctrl_t otp;
static dif_rstmgr_t rstmgr;
static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;

// LC RMA token value in OTP SECRET2 partition.
static const uint8_t kOtpRmaToken[OTP_CTRL_PARAM_RMA_TOKEN_SIZE] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

// Creator Root Key share 0 in OTP SECRET2 partition.
static const uint8_t
    kOtpCreatorRootKeyShare0[OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE] = {
        0x6e, 0x70, 0x48, 0x68, 0xa3, 0x2f, 0xfa, 0x1b, 0xd8, 0x36, 0x4d,
        0x00, 0x79, 0xbd, 0x04, 0xe6, 0x53, 0x18, 0xfc, 0xc3, 0xc9, 0xdd,
        0x39, 0xfa, 0xe0, 0x18, 0x49, 0x69, 0xc9, 0x81, 0x05, 0x17,
};

// Creator Root Key share 1 in OTP SECRET2 partition.
static const uint8_t
    kOtpCreatorRootKeyShare1[OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE] = {
        0x2f, 0x78, 0x6f, 0x93, 0x9a, 0xc4, 0xcf, 0x95, 0xb6, 0xec, 0x61,
        0x76, 0xbd, 0x08, 0x05, 0x0c, 0x09, 0x89, 0xe1, 0x73, 0x4b, 0x0a,
        0x59, 0x1b, 0xdd, 0x34, 0x84, 0x82, 0x32, 0x9a, 0x93, 0x31};

static const uint8_t kOtpCreatorSeed[OTP_CTRL_PARAM_CREATOR_SEED_SIZE] = {
    0x84, 0xab, 0x89, 0x13, 0x79, 0x67, 0xb7, 0x8b, 0xd9, 0x78, 0x54,
    0xb5, 0x02, 0x97, 0x6a, 0x4e, 0x08, 0x34, 0xb8, 0xe5, 0x57, 0xe2,
    0x88, 0xd8, 0xb5, 0xfa, 0x2b, 0xf3, 0x83, 0xbb, 0x11, 0xa5};

static const uint8_t kOtpOwnerSeed[OTP_CTRL_PARAM_OWNER_SEED_SIZE] = {
    0x1b, 0xd5, 0x68, 0xbe, 0x01, 0xb8, 0xe8, 0xfb, 0x69, 0xf4, 0xea,
    0x2c, 0xd9, 0x35, 0x8e, 0xe6, 0x13, 0x11, 0x14, 0xab, 0x22, 0x42,
    0x63, 0xc5, 0xdb, 0xfb, 0xc9, 0xe7, 0x92, 0x46, 0x33, 0x4e};

// Enum that encodes the possible OTP access modes.
typedef enum { kWriteMode, kReadMode, kWriteReadMode } access_mode_t;

// Enum that encodes the boot stage from which to generate an output.
typedef enum { kBootStage1, kBootStage2 } boot_stage_t;

// Enum that encodes whether KeymgrDpe is enabled by LC.
typedef enum { kDisabledByLc, kEnabledByLc } lc_enable_t;

// Enum that encodes the OTP partitions to access.
typedef enum { kSecret2Only, kSecret3Only, kSecret2AndSecret3 } partitions_t;

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
      mmio_region_from_addr(TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR), &lc));
  // OTP
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR), &otp));
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));
  // Rstmgr
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_RSTMGR_AON_BASE_ADDR), &rstmgr));
  // KMAC (init for KeymgrDpe use)
  CHECK_DIF_OK(dif_kmac_init(
      mmio_region_from_addr(TOP_DARJEELING_KMAC_BASE_ADDR), &kmac));
  CHECK_STATUS_OK(kmac_testutils_config(&kmac, true));
  // KeymgrDpe
  CHECK_DIF_OK(dif_keymgr_dpe_init(
      mmio_region_from_addr(TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR), &keymgr_dpe));
}

/**
 * Attempt to write the buffer to the specified address within the specified
 * partition. If exp_result is set to kExpectFailed, the test expects the
 * access to fail with a DAI access error. If exp_result is set to
 * kExpectPassed, the test expects the test to pass without errors.
 */
static void otp_write_test(dif_otp_ctrl_partition_t partition, uint32_t address,
                           const uint8_t *buffer, uint32_t size,
                           exp_test_result_t exp_result) {
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  for (uint32_t i = address; i < address + size; i += sizeof(uint64_t)) {
    uint64_t word;
    memcpy(&word, &buffer[i], sizeof(word));
    CHECK_DIF_OK(dif_otp_ctrl_dai_program64(&otp, partition, i, word));
    CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
    CHECK(address <= INT32_MAX, "address must fit into int32_t");
    CHECK_STATUS_OK(otp_ctrl_testutils_dai_access_error_check(
        &otp, exp_result, (int32_t)address));
  }
}

/**
 * Attempt to read the OTP contents at the specified address within the
 * specified partition, and compares the read data to the data in the buffer. If
 * exp_result is set to kExpectFailed, the test expects the access to fail
 * with a DAI access error, and it also expects the read data to NOT match with
 * the data in the buffer. If exp_result is set to kExpectPassed, the test
 * expects the test to pass without errors and the read data to match with the
 * data in the buffer.
 */
static void otp_read_test(dif_otp_ctrl_partition_t partition, uint32_t address,
                          const uint8_t *buffer, uint32_t size,
                          exp_test_result_t exp_result) {
  CHECK_STATUS_OK(otp_ctrl_testutils_wait_for_dai(&otp));
  for (uint32_t i = address; i < address + size; i += sizeof(uint64_t)) {
    uint64_t got, exp;
    CHECK_DIF_OK(dif_otp_ctrl_dai_read_start(&otp, partition, i));
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
static void otp_write_read_test(access_mode_t access_mode,
                                dif_otp_ctrl_partition_t partition,
                                uint32_t address, const uint8_t *buffer,
                                uint32_t size, exp_test_result_t exp_result) {
  if (access_mode == kWriteMode || access_mode == kWriteReadMode) {
    LOG_INFO("Write test at 0x%x...", address);
    otp_write_test(partition, address, buffer, size, exp_result);
  }
  if (access_mode == kReadMode || access_mode == kWriteReadMode) {
    LOG_INFO("Read test at 0x%x...", address);
    otp_read_test(partition, address, buffer, size, exp_result);
  }
}

/**
 * Test wrapper function that calls the write and read tests above for all
 * objects within the specified partitions.
 */
static void run_otp_access_tests(partitions_t partitions,
                                 access_mode_t access_mode,
                                 exp_test_result_t exp_result) {
  if (partitions == kSecret2Only || partitions == kSecret2AndSecret3) {
    // Silicon Creator (SECRET2 partition) objects:
    // - RMA Token
    otp_write_read_test(
        access_mode, kDifOtpCtrlPartitionSecret2,
        OTP_CTRL_PARAM_RMA_TOKEN_OFFSET - OTP_CTRL_PARAM_SECRET2_OFFSET,
        (uint8_t *)kOtpRmaToken, OTP_CTRL_PARAM_RMA_TOKEN_SIZE, exp_result);
    // - Creator Root Key (two shares)
    otp_write_read_test(access_mode, kDifOtpCtrlPartitionSecret2,
                        OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_OFFSET -
                            OTP_CTRL_PARAM_SECRET2_OFFSET,
                        (uint8_t *)kOtpCreatorRootKeyShare0,
                        OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE0_SIZE,
                        exp_result);
    otp_write_read_test(access_mode, kDifOtpCtrlPartitionSecret2,
                        OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_OFFSET -
                            OTP_CTRL_PARAM_SECRET2_OFFSET,
                        (uint8_t *)kOtpCreatorRootKeyShare1,
                        OTP_CTRL_PARAM_CREATOR_ROOT_KEY_SHARE1_SIZE,
                        exp_result);
    // - Creator Seed
    otp_write_read_test(
        access_mode, kDifOtpCtrlPartitionSecret2,
        OTP_CTRL_PARAM_CREATOR_SEED_OFFSET - OTP_CTRL_PARAM_SECRET2_OFFSET,
        (uint8_t *)kOtpCreatorSeed, OTP_CTRL_PARAM_CREATOR_SEED_SIZE,
        exp_result);
  }
  if (partitions == kSecret3Only || partitions == kSecret2AndSecret3) {
    // Silicon Owner (SECRET3 partition) objects:
    // - Owner Seed
    otp_write_read_test(
        access_mode, kDifOtpCtrlPartitionSecret3,
        OTP_CTRL_PARAM_OWNER_SEED_OFFSET - OTP_CTRL_PARAM_SECRET3_OFFSET,
        (uint8_t *)kOtpOwnerSeed, OTP_CTRL_PARAM_OWNER_SEED_SIZE, exp_result);
  }
}

/**
 * Checks that keymgr_dpe cannot be initialized after reset.
 *
 * We expect initialization to fail for one of two reasons (exclusive or):
 * (a) The current LC state does not allow usage of keymgr_dpe.
 * (b) The Creator Root Key cannot be loaded because the SECRET2 OTP partition
 *     is not locked.
 *
 * @param lc_enable distinguishes between the expected failure reasons
 *                  (see above): kDisabledByLc -> (a); kEnabledByLc -> (b)
 */
static void keymgr_dpe_check_initialize(lc_enable_t lc_enable,
                                        exp_test_result_t exp_result) {
  LOG_INFO("Check that KeymgrDpe %s be initialized after reset...",
           exp_result == kExpectFailed ? "cannot" : "can");
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_check_state(&keymgr_dpe, kDifKeymgrDpeStateReset));
  const dif_result_t init_res =
      dif_keymgr_dpe_initialize(&keymgr_dpe, /*slot_dst_sel=*/0);
  if (lc_enable == kDisabledByLc) {
    CHECK(exp_result == kExpectFailed);
    // We expect that keymgr_dpe is locked entirely, so the initialization does
    // not even start and keymgr_dpe remains in reset.
    CHECK(init_res == kDifLocked,
          "KeymgrDpe is not expected to be available in this LC state.");
    CHECK_STATUS_OK(
        keymgr_dpe_testutils_check_state(&keymgr_dpe, kDifKeymgrDpeStateReset));
  } else {
    // We expect that keymgr_dpe is not locked, so the initialization starts.
    CHECK(init_res == kDifOk);
    CHECK_STATUS_OK(keymgr_dpe_testutils_wait_for_operation_done(&keymgr_dpe));
    // If we expect a failure (because the Creator Root Key is invalid),
    // keymgr_dpe must now be in the Invalid state; otherwise, it must be
    // available.
    const dif_keymgr_dpe_state_t exp_state = exp_result == kExpectFailed
                                                 ? kDifKeymgrDpeStateInvalid
                                                 : kDifKeymgrDpeStateAvailable;
    CHECK_STATUS_OK(keymgr_dpe_testutils_check_state(&keymgr_dpe, exp_state));
  }
}

/**
 * Initialize KeymgrDpe, derive boot stage 0, 1, and 2 (depending on the
 * `boot_stage` argument) keys and generate a SW output.
 */
static void keymgr_dpe_check_can_generate_output(boot_stage_t boot_stage) {
  // Initialize keymgr_dpe and derive boot stage 0 key.
  LOG_INFO("Check that KeymgrDpe can be initialized to boot stage 0 key...");
  keymgr_dpe_check_initialize(kEnabledByLc, kExpectPassed);

  // Derive boot stage 1 key.
  LOG_INFO("Check that KeymgrDpe can derive boot stage 1 key ...");
  const dif_keymgr_dpe_advance_params_t stage1_params = {
      .slot_src_sel = 0,
      .slot_dst_sel = 0,
      .max_key_version = 100,
      .binding_value = {0, 1, 2, 3, 4, 5, 6, 7},
      .slot_policy = 0x1,  // allow child, not exportable, don't retain parent
  };
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_advance_state(&keymgr_dpe, &stage1_params));

  if (boot_stage == kBootStage2) {
    // Derive boot stage 2 key.
    LOG_INFO("Check that KeymgrDpe can derive boot stage 2 key ...");
    const dif_keymgr_dpe_advance_params_t stage2_params = {
        .slot_src_sel = 0,
        .slot_dst_sel = 0,
        .max_key_version = 42,
        .binding_value = {17, 18, 19, 20, 21, 22, 23, 24},
        .slot_policy = 0x5,  // allow child, not exportable, retain parent
    };
    CHECK_STATUS_OK(
        keymgr_dpe_testutils_advance_state(&keymgr_dpe, &stage2_params));
  }

  // Generate SW output from slot 0, which contains the key of boot stage 1 or 2
  // depending on the `boot_stage` argument.
  LOG_INFO("Check that KeymgrDpe can generate SW output ...");
  const dif_keymgr_dpe_generate_params_t gen_params = {
      .sideload_key = false,
      .key_dest = kDifKeymgrDpeKeyDestNone,
      .slot_src_sel = 0,
      .salt = {29, 31, 37, 41, 43, 47, 53, 59},
      .version = 11,
  };
  dif_keymgr_dpe_output_t sw_oup;
  CHECK_STATUS_OK(
      keymgr_dpe_testutils_generate(&keymgr_dpe, &gen_params, &sw_oup));
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
 * signals on the SECRET2 OTP partition as well as of the lc_owner_seed_sw_rw_en
 * and lc_seed_hw_rd_en signals on the SECRET3 OTP partition.  Since it uses the
 * key manager to perform some of the testing, this test also checks the impact
 * of lc_keymgr on the key manager.
 *
 * The SECRET2 and SECRET3 partitions should only be readable/writable by SW in
 * PROD/RMA/DEV.  Once they are locked, each partition is not accessible by SW
 * anymore, but becomes accessible to HW (key manager).
 *
 * The test can be run in different life cycle states and figure out what to
 * check based on the state exposed in the life cycle controller.
 *
 * PROD/DEV/RMA:
 * 1.1) Program the SECRET2 partition and read it back.
 *  .2) Check that key manager initialization errors out (because the SECRET2
 *      partition is not locked and thus the Creator Root Key is not available
 *      to the key manager).
 *  .3) Reset the chip.
 * 2.1) Check that the SECRET2 partition can still be read from SW.
 *  .2) Check that key manager initialization still errors out (because the
 *      SECRET2 partition is still not locked).
 *  .3) Lock the SECRET2 partition.
 *  .4) Program the SECRET3 partition and read it back.
 *  .5) Reset the chip.
 * 3.1) Check that the SECRET2 partition can no longer be read from SW.
 *  .2) Check that the SECRET3 partition can still be read from SW.
 *  .3) Check that key manager can be initialized and a SW output can be
 *      generated from the boot stage 1 key.
 *  .4) Lock the SECRET3 partition.
 *  .5) Reset the chip.
 * 4.1) Check that neither the SECRET2 nor the SECRET3 partition can be read or
 *      written from SW.
 *  .2) Check that key manager can be initialized and a SW output can be
 *      generated from the boot stage 2 key.
 *
 * All other life cycle states:
 * 1) Check that key manager cannot be initialized because it is disabled.
 * 2) Check that the SECRET2 and SECRET3 partitions are not accessible.
 */
bool test_main(void) {
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
        // Program the SECRET2 partition and perform read-back test.
        run_otp_access_tests(kSecret2Only, kWriteReadMode, kExpectPassed);
        // We expect the root key to be invalid at this point, so KeymgrDpe
        // cannot be initialized.
        keymgr_dpe_check_initialize(kEnabledByLc, kExpectFailed);
        reset_chip();

      } else if (rst_info == kDifRstmgrResetInfoSw) {
        bool secret2_digest_computed, secret3_digest_computed;
        CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
            &otp, kDifOtpCtrlPartitionSecret2, &secret2_digest_computed));
        CHECK_DIF_OK(dif_otp_ctrl_is_digest_computed(
            &otp, kDifOtpCtrlPartitionSecret3, &secret3_digest_computed));

        if (!secret2_digest_computed) {
          LOG_INFO("Second access test iteration...");
          CHECK(!secret3_digest_computed,
                "SECRET3 digest should only be computed after the third "
                "iteration.");
          // SECRET2 partition should still be readable from SW.
          run_otp_access_tests(kSecret2Only, kReadMode, kExpectPassed);
          // We expect the root key to still be invalid at this point, since
          // SECRET2 has not been locked yet.
          keymgr_dpe_check_initialize(kEnabledByLc, kExpectFailed);
          // Lock the SECRET2 partition.
          CHECK_STATUS_OK(otp_ctrl_testutils_lock_partition(
              &otp, kDifOtpCtrlPartitionSecret2, 0));
          // Program the SECRET3 partition and perform read-back test.
          run_otp_access_tests(kSecret3Only, kWriteReadMode, kExpectPassed);
          reset_chip();

        } else if (secret2_digest_computed && !secret3_digest_computed) {
          LOG_INFO("Third access test iteration...");
          // SECRET2 partition should no longer be accessible from SW.
          run_otp_access_tests(kSecret2Only, kWriteReadMode, kExpectFailed);
          // SECRET3 partition should still be readable from SW.
          run_otp_access_tests(kSecret3Only, kReadMode, kExpectPassed);
          // It should now be possible to initialize KeymgrDpe and generate an
          // output from the boot stage 1 key.
          keymgr_dpe_check_can_generate_output(kBootStage1);
          // Lock the SECRET3 partition.
          CHECK_STATUS_OK(otp_ctrl_testutils_lock_partition(
              &otp, kDifOtpCtrlPartitionSecret3, 0));
          reset_chip();

        } else {
          CHECK(secret2_digest_computed && secret3_digest_computed);
          LOG_INFO("Fourth access test iteration...");
          // All OTP accesses from SW are disallowed.
          run_otp_access_tests(kSecret2AndSecret3, kWriteReadMode,
                               kExpectFailed);
          // It should now be possible to initialize KeymgrDpe and generate an
          // output from the boot stage 2 key.
          keymgr_dpe_check_can_generate_output(kBootStage2);
          // Test passed.
          return true;
        }

      } else {
        LOG_ERROR("Unexpected reset info 0x%02X", rst_info);
      }

      break;
    default:  // this covers all TEST_UNLOCKED* states.
      // SW accesses to the SECRET2 and SECRET3 partition should error out.
      run_otp_access_tests(kSecret2AndSecret3, kWriteReadMode, kExpectFailed);
      // KeymgrDpe initialization should not work in this state.
      keymgr_dpe_check_initialize(kDisabledByLc, kExpectFailed);
      // Test passed.
      return true;
  }

  return false;
}
