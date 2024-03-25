// Copyright lowRISC contributors.
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
   * kSigverifyEcdsaSuccess = kSigverifyFlashExec`.
   */
  kSigverifyEcdsaSuccess = 0x2f06b4e0,
};


OT_WARN_UNUSED_RESULT
rom_error_t sigverify_ecdsa_verify(const sigverify_ecdsa_p256_buffer_t *signature,
                                 const sigverify_ecdsa_p256_buffer_t *key,
                                 const hmac_digest_t *act_digest,
                                 lifecycle_state_t lc_state,
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
inline uint32_t sigverify_ecdsa_success_to_ok(uint32_t v) {
  return (v << 22 ^ v << 19 ^ v << 3) >> 21;
}

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_ECDSA_P256_VERIFY_H_
