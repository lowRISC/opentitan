// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/ip/otp_ctrl/test/utils/otp_ctrl_testutils.h"

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/log.h"

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

static const uint32_t kNvmCntWords =
    OTP_CTRL_PARAM_EXT_NVM_ANTIREPLAY_FRESHNESS_CNT_SIZE / sizeof(uint32_t) / 2;
static const uint32_t kNvmMaxCnt = kNvmCntWords * 32;

/**
 * Decodes a thermometer encoded 32bit word and returns the count.
 *
 * The faulty_bits argument is zero if the thermometer
 * encoding is correct. In case it is incorrect,
 * the bit position where the thermometer encoding has
 * a "hole" is set to 1.
 *
 * examples:
 *
 * raw_data: 0x0000FFFF returns: 15 faulty_bits: 0x00000000
 * raw_data: 0x3FFFFFFF returns: 29 faulty_bits: 0x00000000
 * raw_data: 0x100FFFFF returns: 28 faulty_bits: 0x0FF00000
 *
 * This function assumes that at least one bit is set in the word.
 */
static uint32_t thermometer_decode(uint32_t raw_data, uint32_t *faulty_bits) {
  uint32_t num_lz = (uint32_t)__builtin_clz(raw_data);
  *faulty_bits = 0x7FFFFFFF;
  *faulty_bits >>= num_lz - 1;
  *faulty_bits &= raw_data ^ (*faulty_bits);
  return 32 - num_lz;
}

status_t otp_ctrl_read_nvm_cnt(const dif_otp_ctrl_t *otp, uint32_t *val,
                               otp_ctrl_nvm_cnt_error_t *err) {
  uint32_t cnt[2];
  *err = kOtpCtrlNvmCntErrOk;
  *val = 0;
  for (uint32_t k = 0; k < kNvmCntWords; k++) {
    // This uses the fast memory-mapped read access path instead of the DAI.
    TRY(dif_otp_ctrl_read_blocking(otp, kDifOtpCtrlPartitionExtNvm,
                                   k * sizeof(uint64_t), cnt, 2));
    // Check whether the redundant copies agree.
    if (cnt[0] != cnt[1]) {
      // If there was no previous corruption, this may still be correctable.
      if (*err != kOtpCtrlNvmCntErrDataLoss) {
        *err = kOtpCtrlNvmCntErrCorrected;
      }
      LOG_INFO("Potentially correctable encoding error in word %d: 0x%x | 0x%x",
               k, cnt[0], cnt[1]);
      cnt[0] |= cnt[1];  // Redundancy scheme uses bitwise OR.
    }
    // If the word is zero, we don't have to do anything here.
    if (cnt[0] != 0) {
      // If this word is nonzero, all previous words must have been all-ones.
      if (*val != (k * 32)) {
        LOG_INFO("Zero value expected in word %d: 0x%x", k, cnt[0]);
        *err = kOtpCtrlNvmCntErrDataLoss;
        // Set the val to the expected value so that decoding can continue
        // even with corrupt encodings.
        *val = k * 32;
      }
      // If this word is all-ones, we just add 32 and continue.
      if (cnt[0] == 0xFFFFFFFF) {
        *val += 32;
        // If the word is neither zero nor all-ones, we can't take shortcuts.
      } else {
        uint32_t faulty_bits;
        *val += thermometer_decode(cnt[0], &faulty_bits);
        if (faulty_bits != 0) {
          LOG_INFO(
              "Corrupt data word %d: 0x%x (corrupt bits 0x%x), total count %d",
              k, cnt[0], faulty_bits, *val);
          *err = kOtpCtrlNvmCntErrDataLoss;
        }
      }
    }
  }
  return OK_STATUS();
}

status_t otp_ctrl_prog_nvm_cnt_word_copies(const dif_otp_ctrl_t *otp,
                                           uint32_t start_address,
                                           uint32_t word, uint32_t len) {
  TRY(otp_ctrl_testutils_wait_for_dai(otp));
  for (uint32_t k = 0; k < len; k++) {
    TRY(dif_otp_ctrl_dai_program32(otp, kDifOtpCtrlPartitionExtNvm,
                                   start_address, word));
    TRY(otp_ctrl_testutils_wait_for_dai(otp));
    TRY(otp_ctrl_dai_write_error_check(otp));
    start_address += sizeof(uint32_t);
  }
  return OK_STATUS();
}

status_t otp_ctrl_prog_nvm_cnt(const dif_otp_ctrl_t *otp, uint32_t val,
                               bool last_word_only,
                               otp_ctrl_nvm_cnt_error_t *err) {
  *err = kOtpCtrlNvmCntErrOk;

  if (val > kNvmMaxCnt) {
    LOG_INFO("%d exceeds the maximum NVM count %d", val, kNvmMaxCnt);
    *err = kOtpCtrlNvmCntErrSaturated;
    return OK_STATUS();
  }

  uint32_t num_full_words = val / 32;
  uint32_t last_word_val = val - num_full_words * 32;

  // In case we only touch the last word and the counter value is a
  // word-aligned all-ones sequence, we just program all-ones to the last
  // word. Otherwise all words up to that last word are programmed.
  if (last_word_only && (last_word_val == 0) && (num_full_words > 0)) {
    TRY(otp_ctrl_prog_nvm_cnt_word_copies(
        otp, (num_full_words - 1) * sizeof(uint64_t), 0xFFFFFFFF, 2));
  } else {
    TRY(otp_ctrl_prog_nvm_cnt_word_copies(otp, 0, 0xFFFFFFFF,
                                          num_full_words * 2));
  }

  // Write remaining bits within the last word.
  if (last_word_val != 0) {
    TRY(otp_ctrl_prog_nvm_cnt_word_copies(
        otp, num_full_words * sizeof(uint64_t), ((1 << last_word_val) - 1), 2));
  }
  return OK_STATUS();
}

status_t otp_ctrl_inc_nvm_cnt(const dif_otp_ctrl_t *otp, uint32_t *val,
                              otp_ctrl_nvm_cnt_error_t *err) {
  TRY(otp_ctrl_read_nvm_cnt(otp, val, err));
  if (*err == kOtpCtrlNvmCntErrOk) {
    TRY(otp_ctrl_prog_nvm_cnt(otp, (*val) + 1, true, err));
    if (*err == kOtpCtrlNvmCntErrOk) {
      (*val)++;
    }
  }
  return OK_STATUS();
}
