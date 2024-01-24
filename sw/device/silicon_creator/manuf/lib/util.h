// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_UTIL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_UTIL_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"

/**
 * Hashes a lifecycle transition token to prepare it to be written to OTP.
 *
 * According to the Lifecycle Controller's specification:
 *
 * "All 128bit lock and unlock tokens are passed through a cryptographic one way
 * function in hardware before the life cycle controller compares them to the
 * provisioned values ...", and
 * "The employed one way function is a 128bit cSHAKE hash with the function name
 * “” and customization string “LC_CTRL”".
 *
 * @param raw_token The raw token to be hashed.
 * @param token_size_bytes The expected hashed token size in bytes.
 * @param[out] hashed_token The hashed token.
 * @return Result of the hash operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_util_hash_lc_transition_token(const uint32_t *raw_token,
                                             size_t token_size_bytes,
                                             uint64_t *hashed_token);

/**
 * Computes a SHA256 digest of the specified OTP partition.
 *
 * Acceptable OTP partitions are:
 * - VendorTest
 * - CreatorSwCfg
 * - OwnerSwCfg
 *
 * For the *SwCfg partitions, the entire hash can be written to the UDS
 * (Creator) certificate DiceTcbInfo extension (specifically the `fwids` field),
 * and the least-significant 64-bits can be written to the corresponding OTP
 * *_SW_CFG partition digest CSRs.
 *
 * @param partition The OTP partition to use.
 * @param[out] output The output hash.
 * @return Result of the hash operation.
 */
OT_WARN_UNUSED_RESULT
status_t manuf_util_hash_otp_partition(const dif_otp_ctrl_t *otp_ctrl,
                                       dif_otp_ctrl_partition_t partition,
                                       otcrypto_word32_buf_t hash);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_LIB_UTIL_H_
