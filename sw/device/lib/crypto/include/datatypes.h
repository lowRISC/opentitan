// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_

#include <stddef.h>
#include <stdint.h>

#ifdef OTCRYPTO_IN_REPO
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/status.h"
#else
#include "freestanding/absl_status.h"
#include "freestanding/defs.h"
#include "freestanding/hardened.h"
#endif

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
typedef enum otcrypto_status_value {
  // Status is OK; no errors.
  kOtcryptoStatusValueOk = (int32_t)0x739,
  // Invalid input arguments; wrong length or invalid type.
  kOtcryptoStatusValueBadArgs = (int32_t)0x8000fea0 | kInvalidArgument,
  // Error after which it is OK to retry (e.g. timeout).
  kOtcryptoStatusValueInternalError = (int32_t)0x80005340 | kAborted,
  // Error after which it is not OK to retry (e.g. integrity check).
  kOtcryptoStatusValueFatalError = (int32_t)0x80006d80 | kFailedPrecondition,
  // An asynchronous operation is still in progress.
  kOtcryptoStatusValueAsyncIncomplete = (int32_t)0x8000ea40 | kUnavailable,
  // TODO: remove all instances of this error before release; it is to track
  // implementations that are not yet complete.
  kOtcryptoStatusValueNotImplemented = (int32_t)0x80008d20 | kUnimplemented,
} otcrypto_status_value_t;

/**
 * Struct to hold a fixed-length byte array.
 *
 * Note: the caller must (1) allocate sufficient space and (2) set the `len`
 * field and `data` pointer when `otcrypto_byte_buf_t` is used for output. The
 * crypto library will throw an error if `len` doesn't match expectations.
 */
typedef struct otcrypto_byte_buf {
  // Pointer to the data.
  uint8_t *data;
  // Length of the data in bytes.
  size_t len;
} otcrypto_byte_buf_t;

/**
 * Struct to hold a constant fixed-length byte array.
 *
 * The const annotations prevent any changes to the byte buffer. It is
 * necessary to have this structure separate from `otcrypto_byte_buf_t` because
 * data pointed to by a struct does not inherit `const`, so `const
 * otcrypto_byte_buf_t` would still allow data to change.
 */
typedef struct otcrypto_const_byte_buf {
  // Pointer to the data.
  const uint8_t *const data;
  // Length of the data in bytes.
  const size_t len;
} otcrypto_const_byte_buf_t;

/**
 * Struct to hold a fixed-length word array.
 *
 * Note: the caller must (1) allocate sufficient space and (2) set the `len`
 * field and `data` pointer when `otcrypto_word32_buf_t` is used for output. The
 * crypto library will throw an error if `len` doesn't match expectations.
 */
typedef struct otcrypto_word32_buf {
  // Pointer to the data.
  uint32_t *data;
  // Length of the data in words.
  size_t len;
} otcrypto_word32_buf_t;

/**
 * Struct to hold a constant fixed-length word array.
 *
 * The const annotations prevent any changes to the word buffer. It is
 * necessary to have this structure separate from `otcrypto_word32_buf_t`
 * because data pointed to by a struct does not inherit `const`, so `const
 * otcrypto_word32_buf_t` would still allow data to change.
 */
typedef struct otcrypto_const_word32_buf {
  // Pointer to the data.
  const uint32_t *const data;
  // Length of the data in words.
  const size_t len;
} otcrypto_const_word32_buf_t;

/**
 * Enum to denote the key type of the handled key.
 *
 * Values are hardened.
 */
typedef enum otcrypto_key_type {
  // Key type AES.
  kOtcryptoKeyTypeAes = 0x8e9,
  // Key type HMAC.
  kOtcryptoKeyTypeHmac = 0xe3f,
  // Key type KMAC.
  kOtcryptoKeyTypeKmac = 0xb74,
  // Key type RSA.
  kOtcryptoKeyTypeRsa = 0x7ee,
  // Key type ECC.
  kOtcryptoKeyTypeEcc = 0x15b,
  // Key type KDF.
  kOtcryptoKeyTypeKdf = 0xb87,
} otcrypto_key_type_t;

/**
 * Enum to specify the AES modes that use a key.
 *
 * This will be used in the `otcrypto_key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum otcrypto_aes_key_mode {
  // Mode AES ECB.
  kOtcryptoAesKeyModeEcb = 0x1b6,
  // Mode AES CBC.
  kOtcryptoAesKeyModeCbc = 0xf3a,
  // Mode AES CFB.
  kOtcryptoAesKeyModeCfb = 0x0f9,
  // Mode AES OFB.
  kOtcryptoAesKeyModeOfb = 0xb49,
  // Mode AES CTR.
  kOtcryptoAesKeyModeCtr = 0x4ce,
  // Mode AES GCM.
  kOtcryptoAesKeyModeGcm = 0xaa5,
  // Mode AES KWP.
  kOtcryptoAesKeyModeKwp = 0x7d5,
} otcrypto_aes_key_mode_t;

/**
 * Enum to specify the HMAC modes that use a key.
 *
 * This will be used in the `otcrypto_key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum otcrypto_hmac_key_mode {
  // Mode HMAC SHA256.
  kOtcryptoHmacKeyModeSha256 = 0x7fd,
  // Mode HMAC SHA384.
  kOtcryptoHmacKeyModeSha384 = 0x43b,
  // Mode HMAC SHA512.
  kOtcryptoHmacKeyModeSha512 = 0x7a2,
} otcrypto_hmac_key_mode_t;

/**
 * Enum to specify the KMAC modes that use a key.
 *
 * This will be used in the `otcrypto_key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum otcrypto_kmac_key_mode {
  // Mode KMAC128.
  kOtcryptoKmacKeyModeKmac128 = 0xa56,
  // Mode KMAC256.
  kOtcryptoKmacKeyModeKmac256 = 0x663,
} otcrypto_kmac_key_mode_t;

/**
 * Enum to specify the RSA modes that use a key.
 *
 * This will be used in the `otcrypto_key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum otcrypto_rsa_key_mode {
  // Mode RSA Sign, RSASSA-PKCS.
  kOtcryptoRsaKeyModeSignPkcs = 0x3d4,
  // Mode RSA Sign, RSASSA-PSS.
  kOtcryptoRsaKeyModeSignPss = 0x761,
  // Mode RSA Encrypt, RSAES-OAEP.
  kOtcryptoRsaKeyModeEncryptOaep = 0x585,
} otcrypto_rsa_key_mode_t;

/**
 * Enum to specify the ECC modes that use a key.
 *
 * This will be used in the `otcrypto_key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum otcrypto_ecc_key_mode {
  // Mode ECDSA.
  kOtcryptoEccKeyModeEcdsa = 0x4e5,
  // Mode ECDH.
  kOtcryptoEccKeyModeEcdh = 0x6bb,
  // Mode Ed25519.
  kOtcryptoEccKeyModeEd25519 = 0xd32,
  // Mode X25519.
  kOtcryptoEccKeyModeX25519 = 0x276,
} otcrypto_ecc_key_mode_t;

/**
 * Enum to specify the KDF modes that use a key.
 *
 * This will be used in the `otcrypto_key_mode_t` struct to indicate the mode
 * for which the provided key is intended for.
 *
 * Values are hardened.
 */
typedef enum otcrypto_kdf_key_mode {
  // Mode KDF-CTR with HMAC as PRF.
  kOtcryptoKdfKeyModeCtrHmac = 0x12f,
  // Mode KDF-KMAC with KMAC128 as PRF.
  kOtcryptoKdfKeyModeKmac128 = 0xe5e,
  // Mode KDF-KMAC with KMAC256 as PRF.
  kOtcryptoKdfKeyModeKmac256 = 0x353,
} otcrypto_kdf_key_mode_t;

/**
 * Enum for opentitan crypto modes that use a key.
 *
 * Denotes the crypto mode for which the provided key is to be used.
 * This `otcrypto_key_mode_t` will be a parameter in the
 * `otcrypto_blinded_key_t` and `otcrypto_unblinded_key_t` structs.
 *
 * Values are hardened.
 */
typedef enum otcrypto_key_mode {
  // Key is intended for AES ECB mode.
  kOtcryptoKeyModeAesEcb = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeEcb,
  // Key is intended for AES CBC mode.
  kOtcryptoKeyModeAesCbc = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeCbc,
  // Key is intended for AES CFB mode.
  kOtcryptoKeyModeAesCfb = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeCfb,
  // Key is intended for AES OFB mode.
  kOtcryptoKeyModeAesOfb = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeOfb,
  // Key is intended for AES CTR mode.
  kOtcryptoKeyModeAesCtr = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeCtr,
  // Key is intended for AES GCM mode.
  kOtcryptoKeyModeAesGcm = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeGcm,
  // Key is intended for AES KWP mode.
  kOtcryptoKeyModeAesKwp = kOtcryptoKeyTypeAes << 16 | kOtcryptoAesKeyModeKwp,
  // Key is intended for HMAC SHA256 mode.
  kOtcryptoKeyModeHmacSha256 =
      kOtcryptoKeyTypeHmac << 16 | kOtcryptoHmacKeyModeSha256,
  // Key is intended for HMAC SHA384 mode.
  kOtcryptoKeyModeHmacSha384 =
      kOtcryptoKeyTypeHmac << 16 | kOtcryptoHmacKeyModeSha384,
  // Key is intended for HMAC SHA512 mode.
  kOtcryptoKeyModeHmacSha512 =
      kOtcryptoKeyTypeHmac << 16 | kOtcryptoHmacKeyModeSha512,
  // Key is intended for KMAC128 mode.
  kOtcryptoKeyModeKmac128 =
      kOtcryptoKeyTypeKmac << 16 | kOtcryptoKmacKeyModeKmac128,
  // Key is intended for KMAC256 mode.
  kOtcryptoKeyModeKmac256 =
      kOtcryptoKeyTypeKmac << 16 | kOtcryptoKmacKeyModeKmac256,
  // Key is intended for RSA signature RSASSA-PKCS mode.
  kOtcryptoKeyModeRsaSignPkcs =
      kOtcryptoKeyTypeRsa << 16 | kOtcryptoRsaKeyModeSignPkcs,
  // Key is intended for RSA signature RSASSA-PSS mode.
  kOtcryptoKeyModeRsaSignPss =
      kOtcryptoKeyTypeRsa << 16 | kOtcryptoRsaKeyModeSignPss,
  // Key is intended for RSA encryption RSAES-OAEP mode.
  kOtcryptoKeyModeRsaEncryptOaep =
      kOtcryptoKeyTypeRsa << 16 | kOtcryptoRsaKeyModeEncryptOaep,
  // Key is intended for ECDSA mode.
  kOtcryptoKeyModeEcdsa = kOtcryptoKeyTypeEcc << 16 | kOtcryptoEccKeyModeEcdsa,
  // Key is intended for ECDH mode.
  kOtcryptoKeyModeEcdh = kOtcryptoKeyTypeEcc << 16 | kOtcryptoEccKeyModeEcdh,
  // Key is intended for Ed25519 mode.
  kOtcryptoKeyModeEd25519 =
      kOtcryptoKeyTypeEcc << 16 | kOtcryptoEccKeyModeEd25519,
  // Key is intended for X25519 mode.
  kOtcryptoKeyModeX25519 =
      kOtcryptoKeyTypeEcc << 16 | kOtcryptoEccKeyModeX25519,
  // Key is intended for KDF-CTR with HMAC as PRF.
  kOtcryptoKeyModeKdfCtrHmac =
      kOtcryptoKeyTypeKdf << 16 | kOtcryptoKdfKeyModeCtrHmac,
  // Key is intended for KDF with KMAC128 as PRF.
  kOtcryptoKeyModeKdfKmac128 =
      kOtcryptoKeyTypeKdf << 16 | kOtcryptoKdfKeyModeKmac128,
  // Key is intended for KDF with KMAC256 as PRF.
  kOtcryptoKeyModeKdfKmac256 =
      kOtcryptoKeyTypeKdf << 16 | kOtcryptoKdfKeyModeKmac256,
} otcrypto_key_mode_t;

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
typedef enum otcrypto_key_security_level {
  // Security level low.
  kOtcryptoKeySecurityLevelLow = 0x1e9,
  // Security level medium.
  kOtcryptoKeySecurityLevelMedium = 0xeab,
  // Security level high.
  kOtcryptoKeySecurityLevelHigh = 0xa7e,
} otcrypto_key_security_level_t;

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
typedef enum otcrypto_lib_version {
  // Version 1.
  kOtcryptoLibVersion1 = 0x7f4,
} otcrypto_lib_version_t;

/**
 * Struct to represent the configuration of a blinded key.
 */
typedef struct otcrypto_key_config {
  // Crypto library version for this key.
  otcrypto_lib_version_t version;
  // Mode for which the key usage is intended.
  otcrypto_key_mode_t key_mode;
  // Length in bytes of the unblinded form of this key.
  size_t key_length;
  // Whether the hardware key manager should produce this key.
  // If this is set to `true`, the keyblob must be exactly 8 words long, where
  // the first word is the version and the remaining 7 words are the salt.
  hardened_bool_t hw_backed;
  // Whether the key can be exported (always false if `hw_backed` is true).
  hardened_bool_t exportable;
  // Key security level.
  otcrypto_key_security_level_t security_level;
} otcrypto_key_config_t;

/**
 * Struct to handle unmasked key type.
 */
typedef struct otcrypto_unblinded_key {
  // Mode for which the key usage is intended.
  otcrypto_key_mode_t key_mode;
  // Key length in bytes.
  size_t key_length;
  // Implementation specific, storage provided by caller.
  uint32_t *key;
  // Implementation specific, checksum for this struct.
  uint32_t checksum;
} otcrypto_unblinded_key_t;

/**
 * Struct to handle masked key type.
 */
typedef struct otcrypto_blinded_key {
  // Key configuration information.
  const otcrypto_key_config_t config;
  // Length of blinded key material in bytes.
  const size_t keyblob_length;
  // Implementation specific, storage provided by caller.
  uint32_t *keyblob;
  // Implementation specific, checksum for this struct.
  uint32_t checksum;
} otcrypto_blinded_key_t;

/**
 * Enum to define supported hashing modes.
 *
 * Values are hardened.
 */
typedef enum otcrypto_hash_mode {
  // SHA2-256 mode.
  kOtcryptoHashModeSha256 = 0x69b,
  // SHA2-384 mode.
  kOtcryptoHashModeSha384 = 0x7ae,
  // SHA2-512 mode.
  kOtcryptoHashModeSha512 = 0x171,
  // SHA3-224 mode.
  kOtcryptoHashModeSha3_224 = 0x516,
  // SHA3-256 mode.
  kOtcryptoHashModeSha3_256 = 0x2d4,
  // SHA3-384 mode.
  kOtcryptoHashModeSha3_384 = 0x267,
  // SHA3-512 mode.
  kOtcryptoHashModeSha3_512 = 0x44d,
  // Shake128 mode.
  kOtcryptoHashXofModeShake128 = 0x5d8,
  // Shake256 mode.
  kOtcryptoHashXofModeShake256 = 0x34a,
  // cShake128 mode.
  kOtcryptoHashXofModeCshake128 = 0x0bd,
  // cShake256 mode.
  kOtcryptoHashXofModeCshake256 = 0x4e2,
} otcrypto_hash_mode_t;

/**
 * Container for a hash digest.
 */
typedef struct otcrypto_hash_digest {
  // Digest type.
  otcrypto_hash_mode_t mode;
  // Digest data.
  uint32_t *data;
  // Digest length in 32-bit words.
  size_t len;
} otcrypto_hash_digest_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_DATATYPES_H_
