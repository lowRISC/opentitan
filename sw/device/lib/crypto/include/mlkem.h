// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MLKEM_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MLKEM_H_

#include "datatypes.h"

/**
 * @file
 * @brief ML-KEM operations for OpenTitan cryptography library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Size of a ML-KEM-1024 public key.
   */
  kOtcryptoMlkem1024PkBytes = 1568,
  kOtcryptoMlkem1024PkWords = kOtcryptoMlkem1024PkBytes / sizeof(uint32_t),
  /**
   * Size of a ML-KEM-1024 secret key.
   */
  kOtcryptoMlkem1024SkBytes = 3168,
  kOtcryptoMlkem1024SkWords = kOtcryptoMlkem1024SkBytes / sizeof(uint32_t),
  /**
   * Size of a ML-KEM-1024 ciphertext.
   */
  kOtcryptoMlkem1024CtBytes = 1568,
  kOtcryptoMlkem1024CtWords = kOtcryptoMlkem1024CtBytes / sizeof(uint32_t),
  /**
   * Size of a ML-KEM-1024 shared secret.
   */
  kOtcryptoMlkem1024SharedSecretBytes = 32,
  kOtcryptoMlkem1024SharedSecretWords =
      kOtcryptoMlkem1024SharedSecretBytes / sizeof(uint32_t),
};

/**
 * Generates a key pair for ML-KEM-1024.
 *
 * @param[out] public_key Pointer to the public key struct.
 * @param[out] secret_key Pointer to the secret key struct.
 * @return Result of the ML-KEM-1024 key generation operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_keygen(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *secret_key);

/**
 * Encapsulates a shared secret for ML-KEM-1024.
 *
 * @param public_key Pointer to the public key struct.
 * @param m Encapsulation randomness (32 bytes).
 * @param[out] ciphertext Pointer to destination ciphertext buffer.
 * @param[out] shared_secret Pointer to destination shared secret struct.
 * @return Result of the ML-KEM-1024 encapsulation operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_encaps(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *m, otcrypto_word32_buf_t *ciphertext,
    otcrypto_blinded_key_t *shared_secret);

/**
 * Decapsulates a shared secret for ML-KEM-1024.
 *
 * @param secret_key Pointer to the secret key struct.
 * @param ciphertext Pointer to input ciphertext.
 * @param[out] shared_secret Pointer to destination shared secret struct.
 * @return Result of the ML-KEM-1024 decapsulation operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_decaps(
    const otcrypto_blinded_key_t *secret_key,
    const otcrypto_const_word32_buf_t *ciphertext,
    otcrypto_blinded_key_t *shared_secret);

/**
 * Starts async key generation for ML-KEM-1024.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_keygen_async_start(void);

/**
 * Finalizes async key generation for ML-KEM-1024.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *secret_key);

/**
 * Starts async encapsulation for ML-KEM-1024.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_encaps_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_word32_buf_t *m);

/**
 * Finalizes async encapsulation for ML-KEM-1024.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_encaps_async_finalize(
    otcrypto_word32_buf_t *ciphertext, otcrypto_blinded_key_t *shared_secret);

/**
 * Starts async decapsulation for ML-KEM-1024.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_decaps_async_start(
    const otcrypto_blinded_key_t *secret_key,
    const otcrypto_const_word32_buf_t *ciphertext);

/**
 * Finalizes async decapsulation for ML-KEM-1024.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_mlkem1024_decaps_async_finalize(
    otcrypto_blinded_key_t *shared_secret);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_MLKEM_H_
