// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/otp_ctrl_testutils.h"

#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

/*
 * OTP the Direct Access Interface (DAI) operation time-out in micro seconds.
 *
 * It is not possible to predict the specific cycle count that a DAI operation
 * takes, thus arbitrary value of 100us is used.
 */
const uint16_t kOtpDaiTimeoutUs = 5000;

/**
 * Checks whether the DAI operation has finished.
 */
static bool dai_finished(const dif_otp_ctrl_t *otp_ctrl) {
  dif_otp_ctrl_status_t status;
  dif_result_t res = dif_otp_ctrl_get_status(otp_ctrl, &status);
  return res == kDifOk &&
         bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiIdle);
}

status_t otp_ctrl_testutils_dai_access_error_check(
    const dif_otp_ctrl_t *otp_ctrl, exp_test_result_t exp_result,
    int32_t address) {
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(otp_ctrl, &status));
  if (exp_result == kExpectFailed) {
    if (!bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiError)) {
      LOG_ERROR("Expected a DAI error for access to 0x%x", address);
    }
    if (status.causes[kDifOtpCtrlStatusCodeDaiError] !=
        kDifOtpCtrlErrorLockedAccess) {
      LOG_ERROR("Expected access locked error for access to 0x%x", address);
    }
  } else {
    if (bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiError)) {
      LOG_ERROR("No DAI error expected for access to 0x%x", address);
    }
    if (status.causes[kDifOtpCtrlStatusCodeDaiError] != kDifOtpCtrlErrorOk) {
      LOG_ERROR("No DAI error code expected for access to 0x%x", address);
    }
  }
  return OK_STATUS();
}

status_t otp_ctrl_testutils_wait_for_dai(const dif_otp_ctrl_t *otp_ctrl) {
  IBEX_TRY_SPIN_FOR(dai_finished(otp_ctrl), kOtpDaiTimeoutUs);
  return OK_STATUS();
}

status_t otp_ctrl_testutils_lock_partition(const dif_otp_ctrl_t *otp,
                                           dif_otp_ctrl_partition_t partition,
                                           uint64_t digest) {
  TRY(dif_otp_ctrl_dai_digest(otp, partition, digest));
  return otp_ctrl_testutils_wait_for_dai(otp);
}

status_t otp_ctrl_testutils_dai_read32(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition,
                                       uint32_t address, uint32_t *result) {
  TRY(otp_ctrl_testutils_wait_for_dai(otp));
  TRY(dif_otp_ctrl_dai_read_start(otp, partition, address));
  TRY(otp_ctrl_testutils_wait_for_dai(otp));
  TRY(dif_otp_ctrl_dai_read32_end(otp, result));
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_read64(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition,
                                       uint32_t address, uint64_t *result) {
  TRY(otp_ctrl_testutils_wait_for_dai(otp));
  TRY(dif_otp_ctrl_dai_read_start(otp, partition, address));
  TRY(otp_ctrl_testutils_wait_for_dai(otp));
  TRY(dif_otp_ctrl_dai_read64_end(otp, result));
  return OK_STATUS();
}

/**
 * Checks if there were any errors found after executing a DAI write transaction
 * to the SECRET2 partition.
 *
 * @param otp otp_ctrl instance
 * @return OK_STATUS if there were no errors detected.
 */
OT_WARN_UNUSED_RESULT
static status_t otp_ctrl_dai_write_error_check(const dif_otp_ctrl_t *otp) {
  dif_otp_ctrl_status_t status;
  TRY(dif_otp_ctrl_get_status(otp, &status));

  // TODO: Check for other OTP errors.
  if (bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiIdle) &&
      !bitfield_bit32_read(status.codes, kDifOtpCtrlStatusCodeDaiError)) {
    return OK_STATUS();
  }
  LOG_ERROR("dai_write_error_check code: 0x%x", status.codes);
  return INTERNAL();
}

status_t otp_ctrl_testutils_dai_write32(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t start_address,
                                        const uint32_t *buffer, size_t len) {
  // Software partitions don't have scrambling or ECC enabled, so it is possible
  // to read the value and compare it against the expected value before
  // performing the write.
  bool check_before_write = (partition == kDifOtpCtrlPartitionCreatorSwCfg ||
                             partition == kDifOtpCtrlPartitionOwnerSwCfg);
  uint32_t stop_address = start_address + (len * sizeof(uint32_t));
  for (uint32_t addr = start_address, i = 0; addr < stop_address;
       addr += sizeof(uint32_t), ++i) {
    uint32_t read_data;
    if (check_before_write) {
      TRY(otp_ctrl_testutils_dai_read32(otp, partition, addr, &read_data));
      if (read_data == buffer[i]) {
        continue;
      }
      if (read_data != 0) {
        LOG_ERROR("OTP partition: %d addr[0x%x] got: 0x%08x, expected: 0x%08x",
                  partition, addr, read_data, buffer[i]);
        return INTERNAL();
      }
    }

    TRY(otp_ctrl_testutils_wait_for_dai(otp));
    TRY(dif_otp_ctrl_dai_program32(otp, partition, addr, buffer[i]));
    TRY(otp_ctrl_testutils_wait_for_dai(otp));
    TRY(otp_ctrl_dai_write_error_check(otp));

    TRY(otp_ctrl_testutils_dai_read32(otp, partition, addr, &read_data));
    if (read_data != buffer[i]) {
      return INTERNAL();
    }
  }
  return OK_STATUS();
}

status_t otp_ctrl_testutils_dai_write64(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t start_address,
                                        const uint64_t *buffer, size_t len) {
  uint32_t stop_address = start_address + (len * sizeof(uint64_t));
  for (uint32_t addr = start_address, i = 0; addr < stop_address;
       addr += sizeof(uint64_t), ++i) {
    TRY(otp_ctrl_testutils_wait_for_dai(otp));
    TRY(dif_otp_ctrl_dai_program64(otp, partition, addr, buffer[i]));
    TRY(otp_ctrl_testutils_wait_for_dai(otp));
    TRY(otp_ctrl_dai_write_error_check(otp));

    uint64_t read_data;
    TRY(otp_ctrl_testutils_dai_read64(otp, partition, addr, &read_data));
    if (read_data != buffer[i]) {
      return INTERNAL();
    }
  }
  return OK_STATUS();
}
