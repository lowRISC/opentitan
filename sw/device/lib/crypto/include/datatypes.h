// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"

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
 * Return values for the crypto library.
 *
 * The crypto library's return value is defined as OpenTitan's internal
 * `status_t` in order to simplify testing. However, informally the library
 * guarantees that the concrete value contained in the status will be one of
 * the members of the `otcrypto_status_value` enum below.
 */
typedef status_t otcrypto_status_t;

/**
 * Possible status values for the cryptolib.
 *
 * As long as the OTCRYPTO_STATUS_DEBUG define is unset, all `otcrypto_status_t`
 * codes returned by the cryptolib should be bit-by-bit equivalent with one of
 * the values in this enum.
 *
 * Values are built to be bit-compatible with OpenTitan's internal `status_t`
 * datatypes. The highest (sign) bit indicates if the value is an error (1) or
 * not (0). For non-error statuses, the rest can be anything; in cryptolib
 * status codes it is always `kHardenedBoolTrue`. For errors:
 *   - The next 15 bits are a module identifier, which is always 0 in the
 *     cryptolib status codes
 *   - The next 11 bits are a line number or other information; in the
 *     cryptolib status codes, it is a hardened value created to have high
 *     Hamming distance with the other valid status codes
 *   - The final 5 bits are an Abseil-compatible error code
 *
 * The hardened values for error codes were generated with:
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 5 -n 11 \
 *      -s 4232058530 --language=sv --avoid-zero
 *
 * Use the same seed value and a larger `-m` argument to generate new values
 * without changing all error codes. Remove the seed (-s argument) to generate
 * completely new 11-bit values.
 */
typedef enum otcrypto_status_value{
  // Status is OK; no errors.
  kOtcryptoStatusOk = (int32_t)0x739,
  // Invalid input arguments; wrong length or invalid type.
  kOtcryptoStatusBadArgs = (int32_t)0x8000fea0 | kInvalidArgument,
  // Error after which it is OK to retry (e.g. timeout).
  kOtcryptoStatusInternalError = (int32_t)0x80005340 | kAborted,
  // Error after which it is not OK to retry (e.g. integrity check).
  kCryptoStatusFatalError = (int32_t)0x80006d80 | kFailedPrecondition,
  // An asynchronous operation is still in progress.
  kOtcryptoStatusAsyncIncomplete = (int32_t)0x8000ea40 | kUnavailable,
  // TODO: remove all instances of this error before release; it is to track
  // implementations that are not yet complete.
  kOtcryptoStatusNotImplemented = (int32_t)0x80008d20 | kUnimplemented,
} otcrypto_status_value_t;

/**
 * Struct to hold a fixed-length byte array.
 *
 * Note: the caller must (1) allocate sufficient space and (2) set the `len`
 * field and `data` pointer when `otcrypto_byte_buf_t` is used for output. The
 * crypto library will throw an error if `len` doesn't match expectations.
 */
typedef struct otcrypto_byte_buf{
  // Length of the data in bytes.
  size_t len;
  // Pointer to the data.
  uint8_t *data;
} otcrypto_byte_buf_t;

/**
 * Struct to hold a constant fixed-length byte array.
 *
 * The const annotations prevent any changes to the byte buffer. It is
 * necessary to have this structure separate from `otcrypto_byte_buf_t` because
 * data pointed to by a struct does not inherit `const`, so `const
 * otcrypto_byte_buf_t` would still allow data to change.
 */
typedef struct otcrypto_const_byte_buf{
  // Length of the data in bytes.
  const size_t len;
  // Pointer to the data.
  const uint8_t *const data;
} otcrypto_const_byte_buf_t;

/**
 * Struct to hold a fixed-length word array.
 *
 * Note: the caller must (1) allocate sufficient space and (2) set the `len`
 * field and `data` pointer when `otcrypto_word32_buf_t` is used for output. The
 * crypto library will throw an error if `len` doesn't match expectations.
 */
typedef struct otcrypto_word32_buf{
  // Length of the data in words.
  size_t len;
  // Pointer to the data.
  uint32_t *data;
} otcrypto_word32_buf_t;

/**
 * Struct to hold a constant fixed-length word array.
 *
 * The const annotations prevent any changes to the word buffer. It is
 * necessary to have this structure separate from `otcrypto_word32_buf_t` because
 * data pointed to by a struct does not inherit `const`, so `const
 * otcrypto_word32_buf_t` would still allow data to change.
 */
typedef struct otcrypto_const_word32_buf{
  // Length of the data in words.
  const size_t len;
  // Pointer to the data.
  const uint32_t *const data;
} otcrypto_const_word32_buf_t;

/**
 * Enum to denote the key type of the handled key.
 *
 * Values are hardened.
 */
typedef enum key_type {
  // Key type AES.
  kKeyTypeAes = 0x8e9,
  // Key type HMAC.
  kKeyTypeHmac = 0xe3f,
  // Key type KMAC.
  kKeyTypeKmac = 0xb74,
  // Key type RSA.
  kKeyTypeRsa = 0x7ee,
  // Key type ECC.
  kKeyTypeEcc = 0x15b,
  // Key type KDF.
  kKeyTypeKdf = 0xb87,
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
  kAesKeyModeEcb = 0x1b6,
  // Mode AES CBC.
  kAesKeyModeCbc = 0xf3a,
  // Mode AES CFB.
  kAesKeyModeCfb = 0x0f9,
  // Mode AES OFB.
  kAesKeyModeOfb = 0xb49,
  // Mode AES CTR.
  kAesKeyModeCtr = 0x4ce,
  // Mode AES GCM.
  kAesKeyModeGcm = 0xaa5,
  // Mode AES KWP.
  kAesKeyModeKwp = 0x7d5,
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
  kHmacKeyModeSha256 = 0x7fd,
  // Mode HMAC SHA384.
  kHmacKeyModeSha384 = 0x43b,
  // Mode HMAC SHA512.
  kHmacKeyModeSha512 = 0x7a2,
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
  kKmacKeyModeKmac128 = 0xa56,
  // Mode KMAC256.
  kKmacKeyModeKmac256 = 0x663,
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
  kRsaKeyModeSignPkcs = 0x3d4,
  // Mode RSA Sign, RSASSA-PSS.
  kRsaKeyModeSignPss = 0x761,
  // Mode RSA Encrypt, RSAES-OAEP.
  kRsaKeyModeEncryptOaep = 0x585,
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
  kEccKeyModeEcdsa = 0x4e5,
  // Mode ECDH.
  kEccKeyModeEcdh = 0x6bb,
  // Mode Ed25519.
  kEccKeyModeEd25519 = 0xd32,
  // Mode X25519.
  kEccKeyModeX25519 = 0x276,
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
  // Mode KDF-CTR with HMAC as PRF.
  kKdfKeyModeCtrHMAC = 0x127,
  // Mode KDF-CTR with KMAC as PRF.
  kKdfKeyModeCtrKMAC = 0x3dd,
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
  // Key is intended for HMAC SHA384 mode.
  kKeyModeHmacSha384 = kKeyTypeHmac << 16 | kHmacKeyModeSha384,
  // Key is intended for HMAC SHA512 mode.
  kKeyModeHmacSha512 = kKeyTypeHmac << 16 | kHmacKeyModeSha512,
  // Key is intended for KMAC128 mode.
  kKeyModeKmac128 = kKeyTypeKmac << 16 | kKmacKeyModeKmac128,
  // Key is intended for KMAC256 mode.
  kKeyModeKmac256 = kKeyTypeKmac << 16 | kKmacKeyModeKmac256,
  // Key is intended for RSA signature RSASSA-PKCS mode.
  kKeyModeRsaSignPkcs = kKeyTypeRsa << 16 | kRsaKeyModeSignPkcs,
  // Key is intended for RSA signature RSASSA-PSS mode.
  kKeyModeRsaSignPss = kKeyTypeRsa << 16 | kRsaKeyModeSignPss,
  // Key is intended for RSA encryption RSAES-OAEP mode.
  kKeyModeRsaEncryptOaep = kKeyTypeRsa << 16 | kRsaKeyModeEncryptOaep,
  // Key is intended for ECDSA mode.
  kKeyModeEcdsa = kKeyTypeEcc << 16 | kEccKeyModeEcdsa,
  // Key is intended for ECDH mode.
  kKeyModeEcdh = kKeyTypeEcc << 16 | kEccKeyModeEcdh,
  // Key is intended for Ed25519 mode.
  kKeyModeEd25519 = kKeyTypeEcc << 16 | kEccKeyModeEd25519,
  // Key is intended for X25519 mode.
  kKeyModeX25519 = kKeyTypeEcc << 16 | kEccKeyModeX25519,
  // Key is intended for KDF-CTR with HMAC as PRF.
  kKeyModeKdfCtrHmac = kKeyTypeKdf << 16 | kKdfKeyModeCtrHMAC,
  // Key is intended for KDF-CTR with KMAC as PRF.
  kKeyModeKdfCtrKmac = kKeyTypeKdf << 16 | kKdfKeyModeCtrKMAC,
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
  kSecurityLevelLow = 0x1e9,
  // Security level medium.
  kSecurityLevelMedium = 0xeab,
  // Security level high.
  kSecurityLevelHigh = 0xa7e,
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
  kCryptoLibVersion1 = 0x7f4,
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
  // If this is set to `true`, the keyblob must be exactly 8 words long, where
  // the first word is the version and the remaining 7 words are the salt.
  hardened_bool_t hw_backed;
  // Whether the key can be exported (always false if `hw_backed` is true).
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

/**
 * Enum to define supported hashing modes.
 *
 * Values are hardened.
 */
typedef enum hash_mode {
  // SHA2-256 mode.
  kHashModeSha256 = 0x69b,
  // SHA2-384 mode.
  kHashModeSha384 = 0x7ae,
  // SHA2-512 mode.
  kHashModeSha512 = 0x171,
  // SHA3-224 mode.
  kHashModeSha3_224 = 0x516,
  // SHA3-256 mode.
  kHashModeSha3_256 = 0x2d4,
  // SHA3-384 mode.
  kHashModeSha3_384 = 0x267,
  // SHA3-512 mode.
  kHashModeSha3_512 = 0x44d,
  // Shake128 mode.
  kHashXofModeShake128 = 0x5d8,
  // Shake256 mode.
  kHashXofModeShake256 = 0x34a,
  // cShake128 mode.
  kHashXofModeCshake128 = 0x0bd,
  // cShake256 mode.
  kHashXofModeCshake256 = 0x4e2,
} hash_mode_t;

/**
 * Container for a hash digest.
 */
typedef struct hash_digest {
  // Digest type.
  hash_mode_t mode;
  // Digest length in 32-bit words.
  size_t len;
  // Digest data.
  uint32_t *data;
} hash_digest_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
