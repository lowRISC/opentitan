// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/otp_ctrl/test/utils/otp_ctrl_testutils.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rstmgr/test/utils/rstmgr_testutils.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

static dif_otp_ctrl_t otp;
static dif_rstmgr_t rstmgr;

OTTF_DEFINE_TEST_CONFIG();

// Need some internal definitions to test corner cases.
static const uint32_t kNvmCntWords =
    OTP_CTRL_PARAM_EXT_NVM_ANTIREPLAY_FRESHNESS_CNT_SIZE / sizeof(uint32_t) / 2;
static const uint32_t kNvmMaxCnt = kNvmCntWords * 32;

// Number of consecutive counter increments.
static const uint32_t kNumIncrements = 3;
// First batch of count offsets for consecutive increment tests
static const uint32_t kCountBases0[] = {0,            // start
                                        32 - 2,       // first word boundary
                                        5 * 32 - 2};  // higher word boundary
// Second batch of count offsets for consecutive increment tests
static const uint32_t kCountBases1[] = {kNvmMaxCnt - 34,  // last word boundary
                                        kNvmMaxCnt - 2};  // last word

/**
 * Programs a base count and performs kNumIncrements +1 count iterations.
 */
static void run_increment_test(const uint32_t *bases, uint32_t num_bases) {
  uint32_t val;
  otp_ctrl_nvm_cnt_error_t err;
  for (uint32_t k = 0; k < num_bases; k++) {
    LOG_INFO("Count base %d of %d", k + 1, num_bases);
    // Program the offset
    CHECK_STATUS_OK(otp_ctrl_prog_nvm_cnt(&otp, bases[k], false, &err));
    CHECK(err == kOtpCtrlNvmCntErrOk, "No encoding errors expected");
    // Do increments
    for (uint32_t i = 1; i <= kNumIncrements; i++) {
      LOG_INFO("Increment %d of %d", i, kNumIncrements);
      CHECK_STATUS_OK(otp_ctrl_inc_nvm_cnt(&otp, &val, &err));
      if (bases[k] + i <= kNvmMaxCnt) {
        CHECK(err == kOtpCtrlNvmCntErrOk, "No encoding errors expected");
        CHECK(val == bases[k] + i,
              "Counter value is incorrect (act: %d, exp: %d)", val,
              bases[k] + i);
      } else {
        CHECK(err == kOtpCtrlNvmCntErrSaturated, "Out of range error expected");
        CHECK(val == kNvmMaxCnt,
              "Counter value is expected to be maximal, but got %d", val);
      }
    }
  }
}

/**
 * Programs error patterns above the current count value in order
 * to test the redundancy mechanism.
 */
static void run_error_test(void) {
  uint32_t cnt[2];
  uint32_t val, expected, addr;
  otp_ctrl_nvm_cnt_error_t err;
  CHECK_STATUS_OK(otp_ctrl_read_nvm_cnt(&otp, &val, &err));
  CHECK(err == kOtpCtrlNvmCntErrOk, "No encoding errors expected");
  // Read the last word value
  CHECK_DIF_OK(dif_otp_ctrl_read_blocking(
      &otp, kDifOtpCtrlPartitionExtNvm, (val / 32) * sizeof(uint64_t), cnt, 2));
  CHECK(cnt[0] > 0 && cnt[0] < 0xFFFF,
        "This word should be nonzero but have at least 16bits left");

  LOG_INFO("Inject correctable error pattern");
  // Program a pattern that can be corrected by OR'ing the two counter copies
  // together. The uppermost nibble is 0x0 so that this words decodes to 28.
  cnt[0] |= 0x0EAD0000;
  cnt[1] |= (~cnt[0]) & 0x0FFFFFFF;
  addr = (val / 32) * sizeof(uint64_t);
  CHECK_STATUS_OK(otp_ctrl_prog_nvm_cnt_word_copies(&otp, addr, cnt[0], 1));
  CHECK_STATUS_OK(otp_ctrl_prog_nvm_cnt_word_copies(
      &otp, addr + sizeof(uint32_t), cnt[1], 1));
  expected = (val / 32) * 32 + 28;
  CHECK_STATUS_OK(otp_ctrl_read_nvm_cnt(&otp, &val, &err));
  CHECK(err == kOtpCtrlNvmCntErrCorrected, "Corrected counter error expected");
  CHECK(val == expected, "Counter value mismatch");

  LOG_INFO("Inject uncorrectable error pattern");
  // Now, we program an error pattern to the next word that cannot be
  // corrected with a simple OR operation (i.e. a pattern with gaps)
  cnt[0] = 0x00000300;
  cnt[1] = 0x00000000;
  // Round up so this gets programmed into the next word.
  addr = ((val + 31) / 32) * sizeof(uint64_t);
  CHECK_STATUS_OK(otp_ctrl_prog_nvm_cnt_word_copies(&otp, addr, cnt[0], 1));
  CHECK_STATUS_OK(otp_ctrl_prog_nvm_cnt_word_copies(
      &otp, addr + sizeof(uint32_t), cnt[1], 1));
  // We've added an extra word which 0x300 decodes to 10 when looking for the
  // highest bit position that is set to 1.
  expected = ((val + 31) / 32) * 32 + 10;
  CHECK_STATUS_OK(otp_ctrl_read_nvm_cnt(&otp, &val, &err));
  CHECK(err == kOtpCtrlNvmCntErrDataLoss, "Counter corruption expected");
  CHECK(val == expected, "Counter value mismatch");
  LOG_INFO("Inject uncorrectable error pattern");
}

/**
 * Initialize the peripherals used in this test.
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_otp_ctrl_init(
      mmio_region_from_addr(TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR), &otp));
  dif_otp_ctrl_config_t config = {
      .check_timeout = 100000,
      .integrity_period_mask = 0x3ffff,
      .consistency_period_mask = 0x3ffffff,
  };
  CHECK_DIF_OK(dif_otp_ctrl_configure(&otp, config));
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_RSTMGR_AON_BASE_ADDR), &rstmgr));
}

bool test_main(void) {
  uint32_t val;
  otp_ctrl_nvm_cnt_error_t err;
  dif_rstmgr_reset_info_bitfield_t rst_info;
  init_peripherals();

  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  if (rst_info & kDifRstmgrResetInfoPor) {
    LOG_INFO("1) Check that the count is zero");
    CHECK_STATUS_OK(otp_ctrl_read_nvm_cnt(&otp, &val, &err));
    CHECK(val == 0, "NVM counter is expected to be zero");
    CHECK(err == kOtpCtrlNvmCntErrOk, "No encoding errors expected");

    LOG_INFO("2) Program count offsets and increment multiple times");
    run_increment_test(kCountBases0, ARRAYSIZE(kCountBases0));

    LOG_INFO("3) Run error injection test");
    run_error_test();

    // Note that this should recover from previously introduced
    // "bad" encodings by just programming all-ones over the corrupted words.
    LOG_INFO("4) Set counter close to max and let it saturate");
    run_increment_test(kCountBases1, ARRAYSIZE(kCountBases1));

    LOG_INFO("5) Reset chip and check that the counter is still maximal");
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    busy_spin_micros(100);
    CHECK(false, "Should have reset before this line");

  } else if (rst_info == kDifRstmgrResetInfoSw) {
    CHECK_STATUS_OK(otp_ctrl_read_nvm_cnt(&otp, &val, &err));
    CHECK(val == kNvmMaxCnt, "Counter value is expected to be maximal");
    CHECK(err == kOtpCtrlNvmCntErrOk, "No encoding errors expected");
    // Test passed
    return true;
  } else {
    LOG_ERROR("Unexpected reset info 0x%02X", rst_info);
  }
  return false;
}
