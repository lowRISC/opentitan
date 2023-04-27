// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_VERIFY_H_

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/spx_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * A non-trivial constant chosen such that `kSigverifySpxSuccess ^
   * kSigverifyRsaSuccess = kSigverifyFlashExec`.
   */
  kSigverifySpxSuccess = 0x8d6c8c17,
  /**
   * A non-trivial constant equal to `kSigverifySpxSuccess`.
   *
   * SPHINCS+ signature verification is always disabled in TEST_UNLOCKED states.
   * In other life cycle states, setting `CREATOR_SW_CFG_SIGVERIFY_SPX_EN` to
   * this value disables SPHINCS+ signature verification and any other value
   * enables it.
   */
  kSigverifySpxDisabledOtp = kSigverifySpxSuccess,
};

/**
 * Get whether SPHINCS+ signature verification is enabled in OTP.
 *
 * This function returns the value of the `CREATOR_SW_CFG_SIGVERIFY_SPX_EN` OTP
 * item unless the lifecycle state of the device is `TEST_UNLOCKED`. For
 * `TEST_UNLOCKED` this function always returns `kSigverifySpxDisabledOtp`.
 *
 * @param lc_state Life cycle state of the device.
 * @return Result of the operation.
 */
uint32_t sigverify_spx_verify_enabled(lifecycle_state_t lc_state);

/**
 * Verifies a SPHINCS+ signature.
 *
 * @param signature Signature to be verified.
 * @param key Signer's SPHINCS+ public key.
 * @param lc_state Life cycle state of the device.
 * @param msg_prefix_1 Optional message prefix.
 * @param msg_prefix_1_len Length of the first prefix.
 * @param msg_prefix_2 Optional message prefix.
 * @param msg_prefix_2_len Length of the second prefix.
 * @param msg Start of the message.
 * @param msg_len Length of the message.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
rom_error_t sigverify_spx_verify(
    const sigverify_spx_signature_t *signature, const sigverify_spx_key_t *key,
    lifecycle_state_t lc_state, const void *msg_prefix_1,
    size_t msg_prefix_1_len, const void *msg_prefix_2, size_t msg_prefix_2_len,
    const void *msg, size_t msg_len, uint32_t *flash_exec);

/**
 * Transforms `kSigverifySpxSuccess` into `kErrorOk`.
 *
 * Callers should transform the result to a suitable error value if it is not
 * `kErrorOk` for ease of debugging.
 *
 * @param v A value.
 * @return `kErrorOk` if `v` is `kSigverifySpxSuccess`.
 */
inline uint32_t sigverify_spx_success_to_ok(uint32_t v) {
  return (v << 22 ^ v << 8 ^ v << 1) >> 20;
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPX_VERIFY_H_
