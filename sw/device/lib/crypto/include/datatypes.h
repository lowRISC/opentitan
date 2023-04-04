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
  kCryptoStatusOK = 0x739,
  // Invalid input arguments; wrong length or invalid type.
  kCryptoStatusBadArgs = 0xb07,
  // Error after which it is OK to retry (e.g. timeout).
  kCryptoStatusInternalError = 0x5c3,
  // Error after which it is not OK to retry (e.g. integrity check).
  kCryptoStatusFatalError = 0xf5c,
  // An asynchronous operation is still in progress.
  kCryptoStatusAsyncIncomplete = 0xae1,
  // TODO: remove all instances of this error before release; it is to track
  // implementations that are not yet complete.
  kCryptoStatusNotImplemented = 0xff,
} crypto_status_t;

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
 * Enum to denote key security level.
 *
 * At high security levels, the crypto library will prioritize
 * protecting the key from sophisticated attacks, even at large
 * performance costs. If the security level is low, the crypto
 * library will still try to protect the key, but may forgo the
 * most costly protections against e.g. sophisticated physical
 * attacks.
 *
 * Values are hardened.
 */
typedef enum crypto_key_security_level {
  // Security level low.
  kSecurityLevelLow = 0xef61,
  // Security level medium.
  kSecurityLevelMedium = 0x33db,
  // Security level high.
  kSecurityLevelHigh = 0xd4bd,
} crypto_key_security_level_t;

/**
 * Enum to denote the crypto library version.
 *
 * In future updates, this enum will be extended to preserve some
 * level of backwards-compatibility despite changes to internal
 * details (for example, the preferred masking scheme for blinded
 * keys).
 *
 * Values are hardened.
 */
typedef enum crypto_lib_version {
  // Version 1.
  kCryptoLibVersion1 = 0x46be,
} crypto_lib_version_t;

/**
 * Struct to represent the configuration of a blinded key.
 */
typedef struct crypto_key_config {
  // Crypto library version for this key.
  crypto_lib_version_t version;
  // Mode for which the key usage is intended.
  key_mode_t key_mode;
  // Length in bytes of the unblinded form of this key.
  size_t key_length;
  // Whether the hardware key manager should produce this key.
  hardened_bool_t hw_backed;
  // Diversification input for key manager (ignored and may be
  // `NULL` if `hw_backed` is false).
  crypto_const_uint8_buf_t diversification_hw_backed;
  // Whether the key should be exportable (if this is true,
  // `hw_backed` must be false).
  hardened_bool_t exportable;
  // Key security level.
  crypto_key_security_level_t security_level;
} crypto_key_config_t;

/**
 * Struct to handle unmasked key type.
 */
typedef struct crypto_unblinded_key {
  // Mode for which the key usage is intended.
  key_mode_t key_mode;
  // Key length in bytes.
  size_t key_length;
  // Implementation specific, storage provided by caller.
  uint32_t *key;
  // Implementation specific, checksum for this struct.
  uint32_t checksum;
} crypto_unblinded_key_t;

/**
 * Struct to handle masked key type.
 */
typedef struct crypto_blinded_key {
  // Key configuration information.
  const crypto_key_config_t config;
  // Length of blinded key material in bytes.
  const size_t keyblob_length;
  // Implementation specific, storage provided by caller.
  uint32_t *keyblob;
  // Implementation specific, checksum for this struct.
  uint32_t checksum;
} crypto_blinded_key_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
