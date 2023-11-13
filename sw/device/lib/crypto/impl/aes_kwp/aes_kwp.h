// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_KWP_AES_KWP_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_KWP_AES_KWP_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/aes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * AES Key Wrapping with Padding (KWP) authenticated encryption.
 *
 * As defined by NIST SP800-38F (section 6.3, algorithm 5).
 *
 * The cipher block mode for the AES key should be ECB, since AES-KWP does not
 * use an IV.
 *
 * The key material must be aligned to 32-bit word boundaries for hardening
 * purposes. The length is still given in bytes, and bytes higher than the
 * length are ignored (although they may be copied, so they should not be
 * uninitialized). The plaintext must be at least 16 bytes long, and must be
 * shorter than 2^32 bytes.
 *
 * The ciphertext buffer must be long enough to hold the *padded* version of
 * the plaintext; this means the length should be rounded up to the next
 * multiple of 64 bits. If the key length is a multiple of 64 bits, then the
 * ciphertext and plaintext should be the same length.
 *
 * @param kek Key encryption key, AES key to encrypt with.
 * @param plaintext Key material to wrap.
 * @param plaintext_len Plaintext length in bytes.
 * @param[out] ciphertext Output buffer.
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_kwp_wrap(const aes_key_t kek, const uint32_t *plaintext,
                      const size_t plaintext_len, uint32_t *ciphertext);

/**
 * AES Key Wrapping with Padding (KWP) authenticated decryption.
 *
 * As defined by NIST SP800-38F (section 6.3, algorithm 6).
 *
 * The cipher block mode for the AES key should be ECB, since AES-KWP does not
 * use an IV.
 *
 * The key material must be aligned to 32-bit word boundaries for hardening
 * purposes. The length is still given in bytes and bytes higher than the given
 * length are ignored (although they may be copied, so they should not be
 * uninitialized). The ciphertext must be at least 24 bytes long, and must be
 * shorter than 2^32 bytes.
 *
 * The output buffer should be the same length as the ciphertext, even if the
 * plaintext is not expected to be as long; this is because the implementation
 * will internally use it as a working buffer.
 *
 * An OK status from this routine does NOT mean that the unwrapping succeeded,
 * only that there were no errors during execution. The caller must check both
 * the returned status and the `success` parameter before reading the
 * plaintext.
 *
 * @param kek Key encryption key, AES key to decrypt with.
 * @param ciphertext Key material to unwrap.
 * @param ciphertext_len Ciphertext length in bytes.
 * @param[out] success Whether the ciphertext was valid.
 * @param[out] plaintext Output buffer, same length as ciphertext
 * @return Error status; OK if no errors
 */
OT_WARN_UNUSED_RESULT
status_t aes_kwp_unwrap(const aes_key_t kek, const uint32_t *ciphertext,
                        const size_t ciphertext_len, hardened_bool_t *success,
                        uint32_t *plaintext);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_AES_KWP_AES_KWP_H_
