// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_OTP_KEYS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_OTP_KEYS_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/rom/sigverify_key_types.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**Maximum number of ECDSA keys supported in OTP. */
  kSigVerifyOtpKeysEcdsaCount = 4,
  /**Maximum number of SPX keys supported in OTP. */
  kSigVerifyOtpKeysSpxCount = 4,
};

/**
 * SRAM representation of the OTP `ROT_CREATOR_AUTH_CODESIGN` partition.
 *
 * The data is loaded into SRAM via `sigverify_otp_keys_init()` and its
 * integrity is verified by `sigverify_otp_keys_check()` before use.
 *
 * Static assertions are used inside the implementation to ensure that the size
 * of the data structure matches the size of the OTP partition.
 */
typedef struct sigverify_otp_keys {
  /**
   * ECDSA P-256 keys.
   */
  sigverify_rom_ecdsa_p256_key_t ecdsa[kSigVerifyOtpKeysEcdsaCount];
  /**
   * SPX keys.
   */
  sigverify_rom_spx_key_t spx[kSigVerifyOtpKeysSpxCount];
  /**
   * HMAC digest of the ECDSA and SPX keys.
   */
  hmac_digest_t integrity_measurement;
} sigverify_otp_keys_t;

/**
 * SRAM representation of the OTP `ROT_CREATOR_AUTH_STATE` partition.
 *
 * The data is loaded into SRAM via `sigverify_otp_keys_init()` and its
 * integrity is verified by `sigverify_otp_keys_check()` before use.
 *
 * Static assertions are used inside the implementation to ensure that the size
 * of the data structure matches the size of the OTP partition.
 */
typedef struct sigverify_otp_key_states {
  /**
   * State of the ECDSA P-256 keys.
   */
  uint32_t ecdsa[kSigVerifyOtpKeysEcdsaCount];
  /**
   * State of the SPX keys.
   */
  uint32_t spx[kSigVerifyOtpKeysSpxCount];
} sigverify_otp_key_states_t;

/**
 * Context for OTP keys loaded into SRAM.
 */
typedef struct sigverify_otp_key_ctx {
  /**
   * ECDSA and SPX keys.
   */
  sigverify_otp_keys_t keys;
  /**
   * Key states.
   */
  sigverify_otp_key_states_t states;
} sigverify_otp_key_ctx_t;

/**
 * Input parameters for `sigverify_otp_keys_get()`.
 */
typedef struct sigverify_otp_keys_get_params {
  /**
   * A key ID.
   */
  uint32_t key_id;
  /**
   * Life cycle state of the device.
   */
  lifecycle_state_t lc_state;
  /**
   * Array in which the requested key is searched for.
   */
  const sigverify_rom_key_header_t *key_array;

  /**
   * Number of keys in `key_array`.
   */
  size_t key_cnt;
  /**
   * Size of each entry in `key_array`.
   */
  size_t key_size;

  uint32_t *key_states;
} sigverify_otp_keys_get_params_t;

/**
 * Initializes the OTP keys context.
 *
 * @param ctx Context for OTP keys loaded into SRAM.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_otp_keys_init(sigverify_otp_key_ctx_t *ctx);

/**
 * Verifies the integrity of the OTP keys.
 *
 * @param ctx Context for OTP keys loaded into SRAM.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t sigverify_otp_keys_check(sigverify_otp_key_ctx_t *ctx);

/**
 * Gets a key from the OTP keys array.
 *
 * @param params Input parameters.
 * @param[out] key A pointer to the requested key.
 * @return The result of the operation.
 */
rom_error_t sigverify_otp_keys_get(sigverify_otp_keys_get_params_t params,
                                   const sigverify_rom_key_header_t **key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_SIGVERIFY_OTP_KEYS_H_
