// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"

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

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_OTP_CTRL_TESTUTILS_H_
