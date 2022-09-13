// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_

#include "sw/device/lib/base/hardened.h"

/**
 * @file
 * @brief Shared datatypes for the OpenTitan cryptography library.
 *
 * This header defines status codes, byte buffer representations, and key
 * representations that are shared between different algorithms within the
 * library.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to handle return values of the crypto API.
 *
 * Values are hardened.
 */
typedef enum crypto_status {
  // Status is OK; no errors.
  kCryptoStatusOK = 0x4d39,
  // Invalid input arguments; wrong length or invalid type.
  kCryptoStatusBadArgs = 0xbd57,
  // Inconsistencies when cross-checking results, witness,checksum.
  kCryptoStatusInternalError = 0x86ba,
  // An asynchronous operation is still in progress.
  kCryptoStatusAsyncIncomplete = 0xd30f,
} crypto_status_t;

/**
 * Enum to handle return values of the verification APIs.
 *
 * Values are hardened.
 */
typedef enum verification_status {
  // Return value for successful verification.
  kVerificationStatusPass = 0x5e34,
  // Return value for unsuccessful verification.
  kVerificationStatusFail = 0x2f4c,
} verification_status_t;

/**
 * Struct to handle crypto data buffer with pointer and length.
 * Note: If the crypto_uint8_buf_t is used for output data, it is
 * expected that the user (1) sets the length of the expected output
 * in the `len` field, and (2) allocates the required space for buffer
 * (`len` bytes). If the output length set by the user doesn’t match
 * the generated output length, an error is thrown and code exits.
 */
typedef struct crypto_uint8_buf {
  // Pointer to the data.
  uint8_t *data;
  // Length of the data in bytes.
  size_t len;
} crypto_uint8_buf_t;

/**
 * Struct to handle crypto const data buffer with pointer and length.
 */
typedef struct crypto_const_uint8_buf {
  // Pointer to the data.
  const uint8_t *data;
  // Length of the data in bytes.
  size_t len;
} crypto_const_uint8_buf_t;

/**
 * Enum to denote the key type of the handled key.
 *
 * Values are hardened.
 */
typedef enum key_type {
  // Key type AES.
  kKeyTypeAes = 0xb51f,
  // Key type HMAC.
  kKeyTypeHmac = 0x196b,
  // Key type KMAC.
  kKeyTypeKmac = 0xe769,
  // Key type RSA.
  kKeyTypeRsa = 0x4fb4,
  // Key type ECC.
  kKeyTypeEcc = 0x3ad6,
  // Key type KDF.
  kKeyTypeKdf = 0xf981,
} key_type_t;

/**
 * Enum to specify the AES modes that use a key.
 *
 * This will be used in the `key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum aes_key_mode {
  // Mode AES ECB.
  kAesKeyModeEcb = 0xd9d7,
  // Mode AES CBC.
  kAesKeyModeCbc = 0xcf6c,
  // Mode AES CFB.
  kAesKeyModeCfb = 0x927a,
  // Mode AES OFB.
  kAesKeyModeOfb = 0x629f,
  // Mode AES CTR.
  kAesKeyModeCtr = 0xf4e1,
  // Mode AES GCM.
  kAesKeyModeGcm = 0x3d0e,
  // Mode AES KWP.
  kAesKeyModeKwp = 0x2bf1,
} aes_key_mode_t;

/**
 * Enum to specify the HMAC modes that use a key.
 *
 * This will be used in the `key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum hmac_key_mode {
  // Mode HMAC SHA256.
  kHmacKeyModeSha256 = 0x64f1,
} hmac_key_mode_t;

/**
 * Enum to specify the KMAC modes that use a key.
 *
 * This will be used in the `key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum kmac_key_mode {
  // Mode KMAC128.
  kKmacKeyModeKmac128 = 0xde4e,
  // Mode KMAC256.
  kKmacKeyModeKmac256 = 0x7863,
} kmac_key_mode_t;

/**
 * Enum to specify the RSA modes that use a key.
 *
 * This will be used in the `key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum rsa_key_mode {
  // Mode RSA Sign, RSASSA-PKCS.
  kRsaKeyModeSignPkcs = 0x473f,
  // Mode RSA Sign, RSASSA-PSS.
  kRsaKeyModeSignPss = 0x9cb3,
} rsa_key_mode_t;

/**
 * Enum to specify the ECC modes that use a key.
 *
 * This will be used in the `key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum ecc_key_mode {
  // Mode ECDSA.
  kEccKeyModeEcdsa = 0xca9a,
  // Mode ECDH.
  kEccKeyModeEcdh = 0xacfd,
  // Mode Ed25519.
  kEccKeyModeEd25519 = 0xf7eb,
  // Mode X25519.
  kEccKeyModeX25519 = 0x50d7,
} ecc_key_mode_t;

/**
 * Enum to specify the KDF modes that use a key.
 *
 * This will be used in the `key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum kdf_key_mode {
  // Mode KDF with HMAC as PRF.
  kKdfKeyModeHMAC = 0x4e6a,
  // Mode KDF with KMAC as PRF.
  kKdfKeyModeKMAC = 0x28af,
} kdf_key_mode_t;

/**
 * Enum for opentitan crypto modes that use a key.
 *
 * Denotes the crypto mode for which the provided key is to be used.
 * This `key_mode_t` will be a parameter in the `crypto_blinded_key_t`
 * and `crypto_unblinded_key_t` structs.
 *
 * Values are hardened.
 */
typedef enum key_mode {
  // Key is intended for AES ECB mode.
  kKeyModeAesEcb = kKeyTypeAes << 16 | kAesKeyModeEcb,
  // Key is intended for AES CBC mode.
  kKeyModeAesCbc = kKeyTypeAes << 16 | kAesKeyModeCbc,
  // Key is intended for AES CFB mode.
  kKeyModeAesCfb = kKeyTypeAes << 16 | kAesKeyModeCfb,
  // Key is intended for AES OFB mode.
  kKeyModeAesOfb = kKeyTypeAes << 16 | kAesKeyModeOfb,
  // Key is intended for AES CTR mode.
  kKeyModeAesCtr = kKeyTypeAes << 16 | kAesKeyModeCtr,
  // Key is intended for AES GCM mode.
  kKeyModeAesGcm = kKeyTypeAes << 16 | kAesKeyModeGcm,
  // Key is intended for AES KWP mode.
  kKeyModeAesKwp = kKeyTypeAes << 16 | kAesKeyModeKwp,
  // Key is intended for HMAC SHA256 mode.
  kKeyModeHmacSha256 = kKeyTypeHmac << 16 | kHmacKeyModeSha256,
  // Key is intended for KMAC128 mode.
  kKeyModeKmac128 = kKeyTypeKmac << 16 | kKmacKeyModeKmac128,
  // Key is intended for KMAC256 mode.
  kKeyModeKmac256 = kKeyTypeKmac << 16 | kKmacKeyModeKmac256,
  // Key is intended for RSA signature RSASSA-PKCS mode.
  kKeyModeRsaSignPkcs = kKeyTypeRsa << 16 | kRsaKeyModeSignPkcs,
  // Key is intended for RSA signature RSASSA-PSS mode.
  kKeyModeRsaSignPss = kKeyTypeRsa << 16 | kRsaKeyModeSignPss,
  // Key is intended for ECDSA mode.
  kKeyModeEcdsa = kKeyTypeEcc << 16 | kEccKeyModeEcdsa,
  // Key is intended for ECDH mode.
  kKeyModeEcdh = kKeyTypeEcc << 16 | kEccKeyModeEcdh,
  // Key is intended for Ed25519 mode.
  kKeyModeEd25519 = kKeyTypeEcc << 16 | kEccKeyModeEd25519,
  // Key is intended for X25519 mode.
  kKeyModeX25519 = kKeyTypeEcc << 16 | kEccKeyModeX25519,
  // Key is intended for KDF with HMAC as PRF.
  kKeyModeKdfHmac = kKeyTypeKdf << 16 | kKdfKeyModeHMAC,
  // Key is intended for KDF with KMAC as PRF.
  kKeyModeKdfKmac = kKeyTypeKdf << 16 | kKdfKeyModeKMAC,
} key_mode_t;

/**
 * Struct to handle unmasked key type.
 */
typedef struct crypto_unblinded_key {
  /**
   * Mode for which the key usage is intended.
   */
  key_mode_t key_mode;
  /**
   * Key length in bytes.
   */
  size_t key_length;
  /**
   * Implementation specific, storage provided by caller.
   *
   * Length in bytes must be equal to `key_length`.
   */
  uint32_t *key;
  /**
   * Implementation specific, checksum for this struct.
   */
  uint32_t checksum;
} crypto_unblinded_key_t;

/**
 * Struct to handle masked key type.
 *
 * Representation is internal to the implementation.
 *
 * Note: The crypto_blinded_key_t struct should include
 * “size_t key_length” and “key_mode_t key_mode” as one of the
 * parameters to check length of the keyblob and the mode intended.
 * The struct should also include a “uint32_t checksum” parameter for
 * integrity purposes. The way the checksum is computed is a
 * implementation specific details.
 */
typedef struct crypto_blinded_key {
  /**
   * Mode for which the key usage is intended.
   */
  key_mode_t key_mode;
  /**
   * Key length in bytes.
   */
  size_t key_length;
  /**
   * Implementation specific, storage provided by caller.
   *
   * Length in bytes must be equal to `key_length`.
   */
  uint32_t *key_blob;
  /**
   * True if and only if this represents a hardware-backed key.
   *
   * In the case of sideloaded keys, `key_blob` contains the handle used to
   * generate the key from the key manager, rather than the actual key
   * material.
   */
  hardened_bool_t sideloaded;
  /**
   * Implementation specific, checksum for this struct.
   */
  uint32_t checksum;
} crypto_blinded_key_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
