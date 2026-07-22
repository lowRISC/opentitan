// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_MLKEM_MLKEM_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_MLKEM_MLKEM_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * ML-KEM-1024 parameter sizes (FIPS 203).
 */
enum {
  kMlkem1024PublicKeyBytes = 1568,
  kMlkem1024PublicKeyWords = kMlkem1024PublicKeyBytes / sizeof(uint32_t),

  kMlkem1024SecretKeyBytes = 3168,
  kMlkem1024SecretKeyWords = kMlkem1024SecretKeyBytes / sizeof(uint32_t),

  kMlkem1024CiphertextBytes = 1568,
  kMlkem1024CiphertextWords = kMlkem1024CiphertextBytes / sizeof(uint32_t),

  kMlkem1024SharedSecretBytes = 32,
  kMlkem1024SharedSecretWords = kMlkem1024SharedSecretBytes / sizeof(uint32_t),
};

/**
 * Mode identifiers for ML-KEM KeyGen.
 */
typedef enum mlkem_keygen_mode {
  kMlkem1024KeygenRndMode = 0x5514edb7,
  kMlkem1024KeygenDetMode = 0xfaacd725,
} mlkem_keygen_mode_t;

/**
 * Start an async ML-KEM-1024 keygen generation (random mode) on OTBN.
 *
 * OTBN will sample random seeds d and z internally using RND hardware.
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_keygen_internal_start(void);

/**
 * Start an async ML-KEM-1024 keygen generation (deterministic mode) on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param d Blinded seed d (64 bytes: 32 bytes share0 + 32 bytes share1).
 * @param z Seed z (32 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_det_keygen_internal_start(
    const otcrypto_blinded_key_t *d, const otcrypto_const_word32_buf_t *z);

/**
 * Finish an async ML-KEM-1024 keygen generation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] public_key Generated public key pk (1568 bytes).
 * @param[out] secret_key Generated secret key sk (3168 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_keygen_internal_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *secret_key);

/**
 * Start an async ML-KEM-1024 encapsulation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param public_key Key for encapsulation (1568 bytes).
 * @param m Input message randomness (32 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_encaps_start(const otcrypto_unblinded_key_t *public_key,
                                const otcrypto_const_word32_buf_t *m);

/**
 * Finish an async ML-KEM-1024 encapsulation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] ciphertext Generated ciphertext (1568 bytes).
 * @param[out] shared_secret Generated shared secret (32 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_encaps_finalize(otcrypto_word32_buf_t *ciphertext,
                                   otcrypto_blinded_key_t *shared_secret);

/**
 * Start an async ML-KEM-1024 decapsulation operation on OTBN.
 *
 * Returns an `OTCRYPTO_ASYNC_INCOMPLETE` error if OTBN is busy.
 *
 * @param secret_key Secret key for decapsulation (3168 bytes).
 * @param ciphertext Input ciphertext (1568 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_decaps_start(const otcrypto_blinded_key_t *secret_key,
                                const otcrypto_const_word32_buf_t *ciphertext);

/**
 * Finish an async ML-KEM-1024 decapsulation operation on OTBN.
 *
 * Blocks until OTBN is idle.
 *
 * @param[out] shared_secret Decapsulated shared secret (32 bytes).
 * @return Result of the operation (OK or error).
 */
status_t mlkem1024_decaps_finalize(otcrypto_blinded_key_t *shared_secret);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_MLKEM_MLKEM_H_
