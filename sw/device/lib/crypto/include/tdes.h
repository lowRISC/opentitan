// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_TDES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_TDES_H_

#include "datatypes.h"

/**
 * @file
 * @brief TDES operations for the OpenTitan cryptography library.
 *
 * WARNING: This module provides a plain software implementation of Triple DES
 * (TDES) and is NOT protected against fault injection (FI) or side-channel
 * analysis (SCA) attacks.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to define TDES mode of operation.
 *
 * Values are hardened.
 */
typedef enum otcrypto_tdes_mode {
  // TDES ECB mode (electronic codebook mode).
  kOtcryptoTdesModeEcb = 0x533,
  // TDES CBC mode (cipher block chaining mode).
  kOtcryptoTdesModeCbc = 0x45d,
  // TDES CFB mode (cipher feedback mode).
  kOtcryptoTdesModeCfb = 0xcd2,
  // TDES OFB mode (output feedback mode).
  kOtcryptoTdesModeOfb = 0x39a,
  // TDES CTR mode (counter mode).
  kOtcryptoTdesModeCtr = 0xd2c,
} otcrypto_tdes_mode_t;

/**
 * Enum to define TDES operation to be performed.
 *
 * Values are hardened.
 */
typedef enum otcrypto_tdes_operation {
  // TDES operation mode encrypt.
  kOtcryptoTdesOperationEncrypt = 0x2b6,
  // TDES operation mode decrypt.
  kOtcryptoTdesOperationDecrypt = 0x5f0,
} otcrypto_tdes_operation_t;

/**
 * Enum to define padding scheme for TDES data.
 *
 * Values are hardened.
 */
typedef enum otcrypto_tdes_padding {
  // Pads with value same as the number of padding bytes.
  kOtcryptoTdesPaddingPkcs7 = 0xe7f,
  // Pads with 0x80 (10000000), followed by zero bytes.
  kOtcryptoTdesPaddingIso9797M2 = 0xfac,
  // Add no padding.
  kOtcryptoTdesPaddingNull = 0x8ce,
} otcrypto_tdes_padding_t;

/**
 * Get the number of blocks needed for the plaintext length and padding mode.
 *
 * This returns the size of the padded plaintext, which is the same as the
 * ciphertext size. Returns `kOtcryptoStatusValueBadArgs` if the padding mode
 * and length are incompatible (for instance, if the padding mode is "no
 * padding" but the input length is not a multiple of the TDES block size).
 *
 * WARNING: This function is part of the plain TDES implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks.
 *
 * @param plaintext_len Plaintext data length in bytes.
 * @param tdes_padding Padding scheme to be used for the data.
 * @param[out] padded_len Size of the padded input or ciphertext.
 * @return Result of the operation. Returns `kOtcryptoStatusValueOk` on
 * success or `kOtcryptoStatusValueBadArgs` if the padding mode or length is
 * invalid.
 */
otcrypto_status_t otcrypto_tdes_padded_plaintext_length(
    size_t plaintext_len, otcrypto_tdes_padding_t tdes_padding,
    size_t *padded_len);

/**
 * Strips padding bytes from a decrypted TDES plaintext buffer.
 *
 * After decryption, `otcrypto_tdes` leaves the padding bytes intact in the
 * output buffer. This function validates the padding according to
 * `tdes_padding` and writes the true plaintext length to `*plaintext_len`. The
 * caller can then use only the first `*plaintext_len` bytes of the buffer. The
 * buffer itself is not modified.
 *
 * WARNING: Exposing whether this function returns a padding error to an
 * external party can enable a padding oracle attack. The caller must ensure
 * that any distinction between valid and invalid padding is not observable by
 * an attacker. Furthermore, this function is part of the plain TDES
 * implementation and is NOT protected against fault injection (FI) or physical
 * side-channel analysis (SCA) attacks.
 *
 * @param padded_plaintext Decrypted data buffer, including padding bytes.
 * @param tdes_padding Padding scheme that was used during encryption.
 * @param[out] plaintext_len Number of real (non-padding) bytes in the buffer.
 * @return Result of the operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments or padding are invalid,
 * or `kOtcryptoStatusValueFatalError` if an internal integrity check fails.
 */
otcrypto_status_t otcrypto_tdes_padding_strip(
    otcrypto_byte_buf_t *padded_plaintext, otcrypto_tdes_padding_t tdes_padding,
    size_t *plaintext_len);

/**
 * Performs the TDES operation.
 *
 * The input data in the `cipher_input` is first padded using the
 * `tdes_padding` scheme and the output is copied to `cipher_output`.
 *
 * WARNING: This function is a plain software implementation and is NOT
 * protected against fault injection (FI) or side-channel analysis (SCA)
 * attacks, regardless of the key security level configured in `key->config`.
 * The key shares in `key` are unmasked in software memory during the
 * operation, and hardware-backed sideload keys (`hw_backed =
 * kHardenedBoolTrue`) are not supported.
 *
 * The caller should allocate space for the `cipher_output` buffer, which is
 * given in bytes by `otcrypto_tdes_padded_plaintext_length`, and set the number
 * of bytes allocated in the `len` field of the output. If the user-set length
 * and the expected length do not match, `kOtcryptoStatusValueBadArgs` will be
 * returned.
 *
 * Note that, during decryption, the padding mode is ignored. This function
 * will NOT check the padding or return an error if the padding is invalid,
 * since doing so could expose a padding oracle (especially in CBC mode).
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param iv Initialization vector, used for CBC, CFB, OFB, CTR modes. May be
 *           NULL if mode is ECB.
 * @param tdes_mode Required TDES mode of operation.
 * @param tdes_operation Required TDES operation (encrypt or decrypt).
 * @param cipher_input Input data to be ciphered.
 * @param tdes_padding Padding scheme to be used for the data.
 * @param[out] cipher_output Output data after cipher operation.
 * @return Result of the cipher operation. Returns `kOtcryptoStatusValueOk` on
 * success, `kOtcryptoStatusValueBadArgs` if arguments, key configuration, or
 * buffer lengths are invalid, or `kOtcryptoStatusValueFatalError` if an
 * internal integrity check fails.
 */
otcrypto_status_t otcrypto_tdes(otcrypto_blinded_key_t *key,
                                otcrypto_word32_buf_t *iv,
                                otcrypto_tdes_mode_t tdes_mode,
                                otcrypto_tdes_operation_t tdes_operation,
                                const otcrypto_const_byte_buf_t *cipher_input,
                                otcrypto_tdes_padding_t tdes_padding,
                                otcrypto_byte_buf_t *cipher_output);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_TDES_H_
