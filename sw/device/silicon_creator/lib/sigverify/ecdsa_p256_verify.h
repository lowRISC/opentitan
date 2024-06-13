// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_VERIFY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_VERIFY_H_

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * A non-trivial constant chosen such that `kSigverifySpxSuccess ^
   * kSigverifyEcdsaSuccess = kSigverifyFlashExec`. The derivation of this value
   * is documented in ecda_p256_verify.c (see `kSigverifyShares` definition).
   */
  kSigverifyEcdsaSuccess = 0x2f06b4e0,
};

/**
 * Verifies an ECDSA-P256 signature.
 *
 * @param signature The signature to verify, little endian.
 * @param key The public key to use for verification, little endian.
 * @param act_digest The actual digest of the signed message.
 * @param[out] flash_exec The partial value to write to the flash_ctrl EXEC
 * register.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_ecdsa_p256_verify(const ecdsa_p256_signature_t *signature,
                                        const ecdsa_p256_public_key_t *key,
                                        const hmac_digest_t *act_digest,
                                        uint32_t *flash_exec);

/**
 * Transforms `kSigverifyEcdsaSuccess` into `kErrorOk`.
 *
 * Callers should transform the result to a suitable error value if it is not
 * `kErrorOk` for ease of debugging.
 *
 * @param v A value.
 * @return `kErrorOk` if `v` is `kSigverifyEcdsaSuccess`.
 */
OT_WARN_UNUSED_RESULT
inline uint32_t sigverify_ecdsa_p256_success_to_ok(uint32_t v) {
  return (v << 22 ^ v << 19 ^ v << 3) >> 21;
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_VERIFY_H_
