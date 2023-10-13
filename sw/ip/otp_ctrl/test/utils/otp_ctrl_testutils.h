// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_IP_OTP_CTRL_TEST_UTILS_OTP_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_IP_OTP_CTRL_TEST_UTILS_OTP_CTRL_TESTUTILS_H_

#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/lib/sw/device/base/status.h"

#include "otp_ctrl_regs.h"  // Generated.

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum that encodes the expectation for the check_dai_access_error function.
 */
typedef enum { kExpectPassed, kExpectFailed } exp_test_result_t;

/**
 * Check whether we got an access error in the DAI.
 *
 * The test passes depending on the expectation argument.
 * I.e., if the expectation is that we get an access error (exp_result ==
 * kExpectFailed), but the DAI does not report any error, the test will fail.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_dai_access_error_check(
    const dif_otp_ctrl_t *otp_ctrl, exp_test_result_t exp_result,
    int32_t address);

/**
 * Waits for the DAI operation to finish (busy wait).
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_wait_for_dai(const dif_otp_ctrl_t *otp_ctrl);

/**
 * Issues a partition lock and waits for the DAI operation to finish (busy
 * wait).
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_lock_partition(const dif_otp_ctrl_t *otp,
                                           dif_otp_ctrl_partition_t partition,
                                           uint64_t digest);

/**
 * Reads a 32bit value from OTP using the DAI interface.
 *
 * @param otp otp_ctrl instance.
 * @param partition OTP partition.
 * @param address Address relative to the start of the `partition`. Must be a
 * 32bit aligned address.
 * @param[out] result The 32bit value result.
 * @return OK_STATUS on successful read.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_dai_read32(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition,
                                       uint32_t address, uint32_t *result);

/**
 * Reads a 64bit value from OTP using the DAI interface.
 *
 * @param otp otp_ctrl instance.
 * @param partition OTP partition.
 * @param address Address relative to the start of the `partition`. Must be a
 * 64bit aligned address.
 * @param[out] result The 64bit value result.
 * @return OK_STATUS on successful read.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_dai_read64(const dif_otp_ctrl_t *otp,
                                       dif_otp_ctrl_partition_t partition,
                                       uint32_t address, uint64_t *result);

/**
 * Writes `len` number of 32bit words from buffer into otp `partition` starting
 * at `start_address` using the DAI interface.
 *
 * For software partitions (`kDifOtpCtrlPartitionCreatorSwCfg` or
 * `kDifOtpCtrlPartitionOwnerSwCfg`), the function will attempt to read the
 * target OTP offsets and skip the write if the existing value matches the
 * expected one. This is possible due to the fact that software partitions are
 * not scrambled nor ECC protected.
 *
 * @param otp otp_ctrl instance.
 * @param partition OTP partition.
 * @param start_address Address relative to the start of the `partition`. Must
 * be a 32bit aligned address.
 * @param buffer The buffer containing the data to be written into OTP.
 * @param len The number of 32bit words to write into otp. `buffer` must have at
 * least `len` 32bit words.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_dai_write32(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t start_address,
                                        const uint32_t *buffer, size_t len);

/**
 * Writes `len` number of 64bit words from buffer into otp `partition` starting
 * at `start_address` using the DAI interface.
 *
 * @param otp otp_ctrl instance.
 * @param partition OTP partition.
 * @param start_address Address relative to the start of the `partition`. Must
 * be a 64bit aligned address.
 * @param buffer The buffer containing the data to be written into OTP.
 * @param len The number of 64bit words to write into otp. `buffer` must have at
 * least `len` 64bit words.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_testutils_dai_write64(const dif_otp_ctrl_t *otp,
                                        dif_otp_ctrl_partition_t partition,
                                        uint32_t start_address,
                                        const uint64_t *buffer, size_t len);

/**
 * NVM Counter Encoding Error types
 *
 * kOtpCtrlNvmCntErrOk        : encoding is consistent
 * kOtpCtrlNvmCntErrCorrected : lossless correction has occurred
 * kOtpCtrlNvmCntErrDataLoss  : the counter encoding is corrupt / lossy
 * kOtpCtrlNvmCntErrSaturated : the counter has saturated and can't be
 * incremented anymore
 */
typedef enum {
  kOtpCtrlNvmCntErrOk,
  kOtpCtrlNvmCntErrCorrected,
  kOtpCtrlNvmCntErrDataLoss,
  kOtpCtrlNvmCntErrSaturated
} otp_ctrl_nvm_cnt_error_t;

/**
 * Reads and decodes the NVM counter
 *
 * This reads and decodes the NVM counter on the fly so that memory
 * requirements are not dependent on how large the counter partition in OTP
 * is. I.e., instead of reading both redundant counter copies from OTP first,
 * this function only reads out two 32bit words of each counter copy at a
 * time. The two counter copies are word-level interleaved for convenience.
 *
 * The counter encoding uses "thermometer" or "strike" encoding, meaning that
 * each bit that is set to 1 represents a counter increment (starting from
 * bit offset 0), e.g.:
 *
 * raw data: 0x00000001, count: 1
 * raw data: 0x0000000F, count: 4
 * raw data: 0x0000FFFF, count: 16
 *
 * The decoding always detects the highest bit that is set to 1 in the entire
 * counter array - but additional checks ensure that the encoding is
 * consistent (the two counter copies must match, and all bits below the
 * highest bit need to be set to ones, whereas all other bits above the
 * highest bit need to be set to ).
 *
 * @param otp otp_ctrl instance.
 * @param val the decoded counter value.
 * @param err kOtpCtrlNvmCntErrOk        if the encoding is ok
 *            kOtpCtrlNvmCntErrCorrected if a lossless correction occurred
 *            kOtpCtrlNvmCntErrDataLoss  if the encoding is corrupt / lossy
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_read_nvm_cnt(const dif_otp_ctrl_t *otp, uint32_t *val,
                               otp_ctrl_nvm_cnt_error_t *err);

/**
 * Programs a 32bit value into consecutive 32bit locations.
 *
 * For writing a redundant 32bit pair, set len to 2.
 *
 * @param otp otp_ctrl instance.
 * @param start_addr the relative address inside the counter partition.
 * @param word the 32bit value to program.
 * @param len number of copies to program into consecutive word locations.
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_prog_nvm_cnt_word_copies(const dif_otp_ctrl_t *otp,
                                           uint32_t start_addr, uint32_t word,
                                           uint32_t len);

/**
 * Encodes and writes the NVM counter
 *
 * This encodes the count value into thermometer encoding and writes it to
 * OTP. Similarly to otp_ctrl_read_nvm_cnt, operations are done while
 * traversing the NVM counter partition in OTP so that memory requirements do
 * not depend on how large that partition is.
 *
 * @param otp otp_ctrl instance.
 * @param val the decoded counter value to program
 * @param last_word_only Set to false to program all non-zero blocks.
 *                        Set to true to only write the block
 *                        affected by the MSB of the current counter state.
 *                        This is a useful option if val has only been
 * incremented by 1, since it completes much faster for larger counts.
 * @param err kOtpCtrlNvmCntErrOk        if the encoding is ok
 *            kOtpCtrlNvmCntErrSaturated the counter cannot be incremented
 * anymore
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_prog_nvm_cnt(const dif_otp_ctrl_t *otp, uint32_t val,
                               bool last_word_only,
                               otp_ctrl_nvm_cnt_error_t *err);

/**
 * Increments the NVM counter by 1
 *
 * This is a short-hand combination of the otp_ctrl_read_nvm_cnt() and
 * otp_ctrl_prog_nvm_cnt() functions. It returns the current counter value
 * stored in OTP.
 *
 * @param otp otp_ctrl instance.
 * @param val the current counter value stored in OTP.
 * @param err kOtpCtrlNvmCntErrOk        if the encoding is ok
 *            kOtpCtrlNvmCntErrCorrected if a lossless correction occurred
 *            kOtpCtrlNvmCntErrDataLoss  if the encoding is corrupt / lossy
 *            kOtpCtrlNvmCntErrSaturated the counter cannot be incremented
 * anymore
 * @return OK_STATUS on success.
 */
OT_WARN_UNUSED_RESULT
status_t otp_ctrl_inc_nvm_cnt(const dif_otp_ctrl_t *otp, uint32_t *val,
                              otp_ctrl_nvm_cnt_error_t *err);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_IP_OTP_CTRL_TEST_UTILS_OTP_CTRL_TESTUTILS_H_
