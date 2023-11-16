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

/**
 * Random values used for programming tests.
 */
enum {
  kPart0Value = 0x04675214,
  kPart1Value = 0xc428c1a1,
  kPart2Value = 0xf51814b4,
};

/**
 * Programs and checks the first word of a partition.
 */
static void prog_test(const dif_otp_ctrl_partition_t partition,
                      uint32_t value) {
  uint32_t result;
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, partition, 0, &result));
  CHECK(result == 0);
  CHECK_STATUS_OK(
      otp_ctrl_testutils_dai_write32(&otp, partition, 0, &value, 1));
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, partition, 0, &result));
  CHECK(result == value);
}

/**
 * Read-locks a partition and checks that reads are locked out.
 */
static void read_lock_test(const dif_otp_ctrl_partition_t partition) {
  uint32_t result;
  bool is_locked;
  dif_otp_ctrl_status_t status;
  // Before locking, reads should work.
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, partition, 0, &result));
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &status));
  CHECK(status.causes[kDifOtpCtrlStatusCodeDaiError] == kDifOtpCtrlErrorOk,
        "Not expecting DAI error");
  // Lock out read access.
  CHECK_DIF_OK(dif_otp_ctrl_lock_reading(&otp, partition));
  CHECK_DIF_OK(dif_otp_ctrl_reading_is_locked(&otp, partition, &is_locked));
  CHECK(is_locked);
  // Check again reading.
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, partition, 0, &result));
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &status));
  CHECK(status.causes[kDifOtpCtrlStatusCodeDaiError] ==
            kDifOtpCtrlErrorLockedAccess,
        "Expecting DAI error");
}

/**
 * Check whether the write lock works.
 */
static void write_lock_test(const dif_otp_ctrl_partition_t partition,
                            uint32_t value, bool exp_write_err) {
  uint32_t result;
  dif_otp_ctrl_status_t status;
  // We still expect the same value that has been written before
  CHECK_STATUS_OK(otp_ctrl_testutils_dai_read32(&otp, partition, 0, &result));
  CHECK(result == value);
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &status));
  CHECK(status.causes[kDifOtpCtrlStatusCodeDaiError] == kDifOtpCtrlErrorOk,
        "Not expecting DAI error");
  CHECK_DIF_OK(dif_otp_ctrl_dai_program32(&otp, partition, 0, value));
  CHECK_DIF_OK(dif_otp_ctrl_get_status(&otp, &status));
  if (exp_write_err) {
    CHECK(status.causes[kDifOtpCtrlStatusCodeDaiError] ==
              kDifOtpCtrlErrorLockedAccess,
          "Expecting DAI error");
  } else {
    CHECK(status.causes[kDifOtpCtrlStatusCodeDaiError] == kDifOtpCtrlErrorOk,
          "Not expecting DAI error");
  }
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
  dif_rstmgr_reset_info_bitfield_t rst_info;
  init_peripherals();

  rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();
  if (rst_info & kDifRstmgrResetInfoPor) {
    LOG_INFO("1) Prog/read tests");
    prog_test(kDifOtpCtrlPartitionOwnerSwCfg, kPart0Value);
    prog_test(kDifOtpCtrlPartitionOwnershipSlotState, kPart1Value);
    prog_test(kDifOtpCtrlPartitionExtNvm, kPart2Value);
    LOG_INFO("2) CSR read lock tests");
    read_lock_test(kDifOtpCtrlPartitionOwnerSwCfg);
    read_lock_test(kDifOtpCtrlPartitionOwnershipSlotState);
    read_lock_test(kDifOtpCtrlPartitionExtNvm);
    LOG_INFO("3) Write-lock partitions and reset chip to check locks");
    // This should succeed.
    CHECK_DIF_OK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionOwnerSwCfg,
                                         0xAAAAAAAA));
    // These two should fail since the partitions do not have a digest.
    CHECK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionOwnershipSlotState,
                                  0xAAAAAAAA) == kDifError);
    CHECK(dif_otp_ctrl_dai_digest(&otp, kDifOtpCtrlPartitionExtNvm,
                                  0xAAAAAAAA) == kDifError);
    // Reset the chip
    CHECK_DIF_OK(dif_rstmgr_software_device_reset(&rstmgr));
    busy_spin_micros(100);
    CHECK(false, "Should have reset before this line");

  } else if (rst_info == kDifRstmgrResetInfoSw) {
    LOG_INFO("4) Check write-locks");
    // Expect an error due to the write-lock.
    write_lock_test(kDifOtpCtrlPartitionOwnerSwCfg, kPart0Value, true);
    // These two cannot be locked, hence we don't expect an error.
    write_lock_test(kDifOtpCtrlPartitionOwnershipSlotState, kPart1Value, false);
    write_lock_test(kDifOtpCtrlPartitionExtNvm, kPart2Value, false);
    // Test passed
    return true;
  } else {
    LOG_ERROR("Unexpected reset info 0x%02X", rst_info);
  }
  return false;
}
