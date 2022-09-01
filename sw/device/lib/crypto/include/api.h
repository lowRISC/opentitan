// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_

/**
 * @brief OS-facing API for the OpenTitan cryptography library.
 *
 * NOTE: This API is a work in progress, and the code here only records the
 * current state. It will continue to change until the API design is finalized.
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
  kCryptoIncorrectInput = 0xbd57,
  // Inconsistencies when cross-checking results, witness,checksum.
  kCryptoStatusInternalError = 0x86ba,
  // An asynchronous operation is still in progress.
  kCryptoStatusAsyncIncomplete = 0xd30f,
} crypto_status_t;

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
 * Enum to denote the AES-GCM tag length.
 *
 * Values are hardened.
 */
typedef enum aead_gcm_tag_len {
  // Tag length 128 bits.
  kAeadGcmTagLen128 = 0xb9ab,
  // Tag length 120 bits.
  kAeadGcmTagLen120 = 0xae53,
  // Tag length 112 bits.
  kAeadGcmTagLen112 = 0x175d,
  // Tag length 104 bits.
  kAeadGcmTagLen104 = 0x68fc,
  // Tag length 96 bits.
  kAeadGcmTagLen96 = 0x7686,
  // Tag length 64 bits.
  kAeadGcmTagLen64 = 0xc6a9,
  // Tag length 32 bits.
  kAeadGcmTagLen32 = 0x4b37,
} aead_gcm_tag_len_t;

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
 * Struct to handle unmasked key type.
 */
typedef struct crypto_unblinded_key {
  // Mode for which the key usage is intended.
  key_mode_t key_mode;
  // Key length.
  size_t key_length;
  // Implementation specific, storage provided by caller.
  uint32_t *key;
  // Implementation specific, checksum for this struct.
  uint32_t checksum;
} crypto_unblinded_key_t;

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
 * Enum to define AES mode of operation.
 *
 * Values are hardened.
 */
typedef enum block_cipher_mode {
  // AES ECB mode (electronic codebook mode).
  kBlockCipherModeEcb = 0x7cae,
  // AES CBC mode (cipher block chaining mode).
  kBlockCipherModeCbc = 0x9736,
  // AES CFB mode (cipher feedback mode).
  kBlockCipherModeCfb = 0xe378,
  // AES OFB mode (output feedback mode).
  kBlockCipherModeOfb = 0x9cdd,
  // AES CTR mode (counter mode).
  kBlockCipherModeCtr = 0x4a1f,
} block_cipher_mode_t;

/**
 * Enum to define AES operation to be performed.
 *
 * Values are hardened.
 */
typedef enum aes_operation {
  // AES operation mode encrypt.
  kAesOperationEncrypt = 0xdea9,
  // AES operation mode decrypt.
  kAesOperationDecrypt = 0x5d5a,
} aes_operation_t;

/**
 * Enum to define padding scheme for AES data.
 *
 * Values are hardened.
 */
typedef enum aes_padding {
  // Pads with value same as the number of padding bytes.
  kAesPaddingPkcs7 = 0xce99,
  // Pads with 0x80 (10000000), followed by zero bytes.
  kAesPaddingIso9797M2 = 0xb377,
  // Pads with 0x00 bytes.
  kAesPaddingIso9797M1 = 0x49eb,
  // Pads with random bytes, last byte is no. of padded bytes.
  kAesPaddingRandom = 0x746c,
  // Pads with 0x00 bytes, last byte is no. of padded bytes.
  kAesPaddingX923 = 0xed32,
  // Add no padding.
  kAesPaddingNull = 0x259f,
} aes_padding_t;

/**
 * Enum to define supported hashing modes.
 *
 * Values are hardened.
 */
typedef enum hash_mode {
  // SHA2-256 mode.
  kHashModeSha256 = 0x6dc2,
  // SHA2-384 mode.
  kHashModeSha384 = 0xdafb,
  // SHA2-512 mode.
  kHashModeSha512 = 0xb626,
  // SHA3-224 mode.
  kHashModeSha3_224 = 0xf51d,
  // SHA3-256 mode.
  kHashModeSha3_256 = 0x196e,
  // SHA3-384 mode.
  kHashModeSha3_384 = 0x14f5,
  // SHA3-512 mode.
  kHashModeSha3_512 = 0x62cd,
} hash_mode_t;

/**
 * Enum to define the supported extendable-output functions.
 *
 * Values are hardened.
 */
typedef enum xof_mode {
  // Shake128 mode.
  kXofModeSha3Shake128 = 0x2bb4,
  // Shake256 mode.
  kXofModeSha3Shake256 = 0x4778,
  // cShake128 mode.
  kXofModeSha3Cshake128 = 0x8f45,
  // cShake256 mode.
  kXofModeSha3Cshake256 = 0x8c9e,
} xof_mode_t;

/**
 * Enum to define MAC mode.
 *
 * Values are hardened.
 */
typedef enum mac_mode {
  // HMAC-SHA2-256 mode.
  kMacModeHmacSha256 = 0x953c,
  // KMAC128 mode.
  kMacModeKmac128 = 0x69b6,
  // KMAC256 mode.
  kMacModeKmac256 = 0xee62,
} mac_mode_t;

/**
 * Enum to define padding scheme for RSA data.
 *
 * Values are hardened.
 */
typedef enum rsa_padding {
  // Pads input data according to the PKCS#1 (v1.5) scheme.
  kRsaPaddingPkcs = 0x9f44,
  // Pads input data according to the PKCS#1-PSS scheme.
  kRsaPaddingPss = 0x88cf,
} rsa_padding_t;

/**
 * Enum to define hash modes for RSA schemes.
 *
 * Aligning with existing hash modes. Values are hardened.
 */
typedef enum rsa_hash {
  // SHA2-256 hashing mode for RSA.
  kRsaHashSha256 = 0xed4b,
  // SHA2-384 hashing mode for RSA.
  kRsaHashSha384 = 0x5dd0,
  // SHA2-512 hashing mode for RSA.
  kRsaHashSha512 = 0x0bab,
  // SHA3-384 hashing mode for RSA.
  kRsaHashSha3_384 = 0x65b7,
} rsa_hash_t;

/**
 * Struct to handle the RSA private exponent and modulus.
 */
typedef struct rsa_private_key {
  // Unblinded key struct with RSA modulus.
  crypto_unblinded_key_t n;
  // Blinded key struct with RSA private exponent.
  crypto_blinded_key_t d;
} rsa_private_key_t;

/**
 * Enum to define possible lengths of RSA (public) keys.
 *
 * Values are hardened.
 */
typedef enum rsa_key_size {
  // 2048-bit RSA key.
  kRsaKeySize2048 = 0xa74d,
  // 3072-bit RSA key.
  kRsaKeySize3072 = 0x7fc6,
  // 4096-bit RSA key.
  kRsaKeySize4096 = 0xf07a,
} rsa_key_size_t;

/**
 * Struct to handle the RSA public exponent and modulus.
 */
typedef struct rsa_public_key {
  // Unblinded key struct with RSA modulus.
  crypto_unblinded_key_t n;
  // Blinded key struct with RSA public exponent.
  crypto_unblinded_key_t e;
} rsa_public_key_t;

/**
 * Struct to handle ECDSA or EdDSA signatures.
 */
typedef struct ecc_signature {
  // Length of ECC signature R parameter, in bytes.
  size_t len_r;
  // ECC signature R parameter.
  uint32_t *r;
  // Length of ECC signature S parameter, in bytes.
  size_t len_s;
  // ECC signature S parameter.
  uint32_t *s;
} ecc_signature_t;

/**
 * Enum to define EdDSA mode for signature.
 *
 * Values are hardened.
 */
typedef enum eddsa_sign_mode {
  // Signature mode EdDSA.
  kEddsaSignModeEdDSA = 0x4fd1,
  // Signature mode Hashed EdDSA.
  kEddsaSignModeHashEdDSA = 0x9bed,
} eddsa_sign_mode_t;

/**
 * Struct to handle ECDSA or ECDH public key type.
 *
 * Length of public key coordinates (x,y) follows len(p).
 */
typedef struct ecc_public_key {
  // ECC public key x coordinate.
  crypto_unblinded_key_t x;
  // ECC public key y coordinate.
  crypto_unblinded_key_t y;
} ecc_public_key_t;

/**
 * Struct for domain parameters of a custom Weierstrass curve.
 */
typedef struct ecc_domain {
  // Prime P (modulus of coordinate finite field).
  crypto_const_uint8_buf_t p;
  // Coefficient a.
  crypto_const_uint8_buf_t a;
  // Coefficient b.
  crypto_const_uint8_buf_t b;
  // q (order of G).
  crypto_const_uint8_buf_t q;
  // Value of x coordinate of G (basepoint). Same length as p.
  const uint32_t *gx;
  // Value of y coordinate of G (basepoint). Same length as p.
  const uint32_t *gy;
  // Cofactor of the curve.
  const uint32_t cofactor;
  // Checksum value of the parameters.
  uint32_t checksum;
} ecc_domain_t;

/**
 * Enum to define the type of elliptic curve used for the operation.
 *
 * Values are hardened.
 */
typedef enum ecc_curve_type {
  // Generic Weierstrass curve, with custom domain parameters.
  kEccCurveTypeCustom = 0xf93c,
  // Named Weierstrass curve - NIST P256.
  kEccCurveTypeNistP256 = 0xe1e7,
  // Named Weierstrass curve - NIST P384.
  kEccCurveTypeNistP384 = 0x6a2b,
  // Named Weierstrass curve - Brainpool P256r1.
  kEccCurveTypeBrainpoolP256R1 = 0x5e96,
} ecc_curve_type_t;

/**
 * Struct for ECC curve used for ECDSA / ECDH operation.
 *
 * Values are hardened.
 */
typedef struct ecc_curve {
  // Type of the Weierstrass curve, custom curve or named curve.
  ecc_curve_type_t curve_type;
  // Domain parameters for a custom Weierstrass curve.
  ecc_domain_t domain_parameter;
} ecc_curve_t;

/**
 * Enum to define the supported KDF constructions.
 *
 * Values are hardened.
 */
typedef enum kdf_type {
  // KDF construction with HMAC as a PRF.
  kKdfTypeHmac = 0xfa3b,
  // KDF construction with KMAC as a PRF.
  kKdfTypeKmac = 0x0f47,
} kdf_type_t;

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
typedef struct crypto_blinded_key crypto_blinded_key_t;

/**
 * Generic hash context.
 *
 * Representation is internal to the hash implementation; initialize
 * with #otcrypto_hash_init.
 */
typedef struct hash_context hash_context_t;

/**
 * Generic hmac context.
 *
 * Representation is internal to the hmac implementation; initialize
 * with #otcrypto_hmac_init.
 */
typedef struct hmac_context hmac_context_t;

/**
 * Context for GCM GHASH operation.
 *
 * Representation is internal to the hmac implementation; initialize
 * with #otcrypto_gcm_ghash_init.
 */
typedef struct gcm_ghash_context gcm_ghash_context_t;

/**
 * DRBG state.
 *
 * Representation is internal to the drbg implementation; initialize
 * with #otcrypto_drbg_instantiate or
 * #otcrypto_drbg_manual_instantiate.
 *
 * Note: The drbg_state_t struct along with V and K, should include:
 * drbg_entropy_mode: To indicate the entropy mode used. Also used to
 * disallow mixing of auto entropy and manual entropy DRBG operations.
 * reseed_counter: To indicate the number of requests for pseudorandom
 * bits since instantiation or reseeding.
 * security_strength: To indicate security strength of the DRBG
 * instantiation.
 * prediction_resistance_flag: To indicate if prediction resistance is
 * required.
 * drbg_mechanism: To indicate if CTR_DRBG or HMAC_DRBG is used for
 * the DRBG instantiation.
 */
typedef struct drbg_state drbg_state_t;

/**
 * Performs the AES initialization operation.
 *
 * The `aes_mode` and `aes_operation` are selected and the `key`, `iv`
 * are loaded into the register.
 *
 * @param key Pointer to the blinded key struct with key shares
 * @param iv Initialization vector, used for CBC, CFB, OFB, CTR modes
 * @param aes_mode Required AES mode of operation
 * @param aes_operation Required AES operation (encrypt or decrypt)
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t otcrypto_aes_init(const crypto_blinded_key_t *key,
                                  crypto_uint8_buf_t iv,
                                  block_cipher_mode_t aes_mode,
                                  aes_operation_t aes_operation);

/**
 * Performs the AES cipher operation.
 *
 * The #otcrypto_aes_init should be called before this function,
 * to initialize the key, AES mode and AES cipher operation.
 *
 * The input data in the `cipher_input` is first padded using the
 * `aes_padding` scheme and the output is copied to `cipher_output`.
 *
 * The caller should allocate space for the `cipher_output` buffer,
 * (same length as input), and set the length of expected output in
 * the `len` field of the output. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * @param cipher_input Input data to be ciphered
 * @param aes_padding Padding scheme to be used for the data
 * @param cipher_output Output data after cipher operation
 * @return crypto_status_t The result of the cipher operation
 */
crypto_status_t otcrypto_aes_cipher(crypto_const_uint8_buf_t cipher_input,
                                    aes_padding_t aes_padding,
                                    crypto_uint8_buf_t *cipher_output);

/**
 * Performs the AES-GCM authenticated encryption operation.
 *
 * This function encrypts the input `plaintext` to produce an
 * output `ciphertext`. Together it generates an authentication
 * tag `auth_tag` on the ciphered data and any non-confidential
 * additional authenticated data `aad`.
 *
 * The caller should allocate space for the `ciphertext` buffer,
 * (same length as input), `auth_tag` buffer (same as tag_len), and
 * set the length of expected outputs in the `len` field of
 * `ciphertext` and `auth_tag`. If the user-set length and the output
 * length does not match, an error message will be returned.
 *
 * @param key Pointer to the blinded gcm-key struct
 * @param plaintext Input data to be encrypted and authenticated
 * @param iv Initialization vector for the encryption function
 * @param aad Additional authenticated data
 * @param tag_len Length of authentication tag to be generated
 * @param ciphertext Encrypted output data, same length as input data
 * @param auth_tag Generated authentication tag
 * @return crypto_status_t Result of the authenticated encryption
 * operation
 */
crypto_status_t otcrypto_aes_encrypt_gcm(
    const crypto_blinded_key_t *key, crypto_const_uint8_buf_t plaintext,
    crypto_uint8_buf_t iv, crypto_uint8_buf_t aad, aead_gcm_tag_len_t tag_len,
    crypto_uint8_buf_t *ciphertext, crypto_uint8_buf_t *auth_tag);

/**
 * Performs the AES-GCM authenticated decryption operation.
 *
 * This function first verifies if the authentication tag `auth_tag`
 * matches the internally generated tag. Upon verification, the
 * function decrypts the input `ciphertext` to get a `plaintext data.
 *
 * The caller should allocate space for the `plaintext` buffer,
 * (same length as ciphertext), and set the length of expected output
 * in the `len` field of `plaintext`. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * @param key Pointer to the blinded gcm-key struct
 * @param ciphertext Input data to be decrypted
 * @param iv Initialization vector for the decryption function
 * @param aad Additional authenticated data
 * @param auth_tag Authentication tag to be verified
 * @param plaintext Decrypted plaintext data, same len as input data
 * @return crypto_status_t Result of the authenticated decryption
 * operation
 */
crypto_status_t otcrypto_aes_decrypt_gcm(const crypto_blinded_key_t *key,
                                         crypto_const_uint8_buf_t ciphertext,
                                         crypto_uint8_buf_t iv,
                                         crypto_uint8_buf_t aad,
                                         crypto_uint8_buf_t auth_tag,
                                         crypto_uint8_buf_t *plaintext);

/**
 * Internal GHASH operation of Galois Counter Mode (GCM).
 *
 * GHASH is an operation internal to GCM. It can be used to create
 * custom implementations that do not adhere to the AES-GCM encryption
 * and decryption API provided here. However, custom GCM constructs
 * can be dangerous; for most use cases, prefer the provided
 * encryption and decryption operations.
 *
 * This function initializes the GHASH context and must be called
 * to create a context object.
 *
 * @param hash_subkey Hash subkey (H), 16 bytes
 * @param ctx Output GHASH context object, caller-allocated
 * @return crypto_status_t Result of the operation
 */
crypto_status_t otcrypto_gcm_ghash_init(const crypto_blinded_key_t *hash_subkey,
                                        gcm_ghash_context_t *ctx);

/**
 * Internal GHASH operation of Galois Counter Mode (GCM).
 *
 * GHASH is an operation internal to GCM. It can be used to create
 * custom implementations that do not adhere to the AES-GCM encryption
 * and decryption API provided here. However, custom GCM constructs
 * can be dangerous; for most use cases, prefer the provided
 * encryption and decryption operations.
 *
 * This operation adds the input buffer to the message that will
 * be hashed and updates the GHASH context. If the input length is
 * not a multiple of 128 bits, it will be right-padded with zeros.
 * The input length must not be zero.
 *
 * @param ctx GHASH context object
 * @param input Input buffer
 * @return crypto_status_t Result of the operation
 */
crypto_status_t otcrypto_gcm_ghash_update(gcm_ghash_context_t *ctx,
                                          crypto_const_uint8_buf_t input);

/**
 * Internal GHASH operation of Galois Counter Mode (GCM).
 *
 * GHASH is an operation internal to GCM. It can be used to create
 * custom implementations that do not adhere to the AES-GCM encryption
 * and decryption API provided here. However, custom GCM constructs
 * can be dangerous; for most use cases, prefer the provided
 * encryption and decryption operations.
 *
 * This operation signals that all input has been provided and
 * extracts the digest from the GHASH context. The digest buffer must
 * be 16 bytes.
 *
 * @param ctx GHASH context object
 * @param digest Output buffer for digest, 16 bytes
 * @return crypto_status_t Result of the operation
 */
crypto_status_t otcrypto_gcm_ghash_final(gcm_ghash_context_t *ctx,
                                         crypto_uint8_buf_t digest);

/**
 * Internal AES-GCTR operation of AES Galois Counter Mode (AES-GCM).
 *
 * GCTR is an operation internal to AES-GCM and is based on AES-CTR.
 * It can be used to create custom implementations that do not adhere
 * to the AES-GCM encryption and decryption API provided here.
 * However, custom GCM constructs can be dangerous; for most use
 * cases, prefer the provided encryption and decryption operations.
 *
 * The caller-allocated output buffer must be the same length as the
 * input.
 *
 * @param key AES key for the GCTR operation
 * @param input Input buffer
 * @param output Output buffer (same length as input)
 * @return crypto_status_t Result of the operation
 */
crypto_status_t otcrypto_aes_gcm_gctr(const crypto_blinded_key_t *key,
                                      crypto_const_uint8_buf_t input,
                                      crypto_uint8_buf_t output);

/**
 * Performs the AES-KWP authenticated encryption operation.
 *
 * This encrypt function takes an input key `key_to_wrap` and using
 * the encryption key `key_kek` outputs a wrapped key `wrapped_key`.
 *
 * The caller should allocate space for the `wrapped_key` buffer,
 * (same len as `key_to_wrap`), and set the length of expected output
 * in the `len` field of `wrapped_key`. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * @param key_to_wrap Pointer to the blinded key to be wrapped
 * @param key_kek Input Pointer to the blinded encryption key
 * @param wrapped_key Pointer to the output wrapped key
 * @return crypto_status_t Result of the aes-kwp encrypt operation
 */
crypto_status_t otcrypto_aes_kwp_encrypt(
    const crypto_blinded_key_t *key_to_wrap,
    const crypto_blinded_key_t *key_kek, crypto_uint8_buf_t *wrapped_key);

/**
 * Performs the AES-KWP authenticated decryption operation.
 *
 * This decrypt function takes a wrapped key `wrapped_key` and using
 * encryption key `key_kek` outputs an unwrapped key `unwrapped_key`.
 *
 * @param wrapped_key Pointer to the input wrapped key
 * @param key_kek Input Pointer to the blinded encryption key
 * @param unwrapped_key Pointer to the output unwrapped key struct
 * @return crypto_status_t Result of the aes-kwp decrypt operation
 */
crypto_status_t otcrypto_aes_kwp_decrypt(crypto_const_uint8_buf_t wrapped_key,
                                         const crypto_blinded_key_t *key_kek,
                                         crypto_blinded_key_t *unwrapped_key);

/**
 * Performs the required hash function on the input data.
 *
 * The caller should allocate space for the `digest` buffer, (expected
 * length depends on `hash_mode`, refer table-1), and set the length
 * of expected output in the `len` field of `digest`. If the user-set
 * length and the output length does not match, an error message will
 * be returned.
 *
 * This function hashes the `input_message` using the `hash_mode_t`
 * hash function and returns a `digest`.
 *
 * @param input_message Input message to be hashed
 * @param hash_mode Required hash mode for the digest
 * @param digest Output digest after hashing the input message
 * @return crypto_status_t Result of the hash operation
 */
crypto_status_t otcrypto_hash(crypto_const_uint8_buf_t input_message,
                              hash_mode_t hash_mode,
                              crypto_uint8_buf_t *digest);

/**
 * Performs the required extendable output function on the input data.
 *
 * The `function_name_string` is used by NIST to define functions
 * based on cSHAKE. When no function other than cSHAKE is desired; it
 * can be empty. The `customization_string` is used to define a
 * variant of the cSHAKE function. If no customization is desired it
 * can be empty. The `function_name_string` and `customization_string`
 * are ignored when the `xof_mode` is set to kHashModeSha3Shake128 or
 * kHashModeSha3Shake256.
 *
 * The caller should allocate space for the `digest` buffer,
 * (expected length same as `required_output_len`), and set the length
 * of expected output in the `len` field of `digest`. If the user-set
 * length and the output length does not match, an error message will
 * be returned.
 *
 * @param input_message Input message for extendable output function
 * @param hash_mode Required extendable output function
 * @param function_name_string NIST Function name string
 * @param customization_string Customization string for cSHAKE
 * @param required_output_len Required output length, in bytes
 * @param digest Output from the extendable output function
 * @return crypto_status_t Result of the xof operation
 */
crypto_status_t otcrypto_xof(crypto_const_uint8_buf_t input_message,
                             xof_mode_t xof_mode,
                             crypto_uint8_buf_t function_name_string,
                             crypto_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *digest);

/**
 * Performs the INIT operation for a cryptographic hash function.
 *
 * Initializes the generic hash context. The required hash mode is
 * selected through the `hash_mode` parameter. Only `kHashModeSha256`,
 * `kHashModeSha384` and `kHashModeSha512` are supported. Other modes
 * are not supported and an error would be returned.
 *
 * Populates the hash context with the selected hash mode and its
 * digest and block sizes. The structure of hash context and how it
 * populates the required fields are internal to the specific hash
 * implementation.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param hash_mode Required hash mode
 * @return crypto_status_t Result of the hash init operation
 */
crypto_status_t otcrypto_hash_init(hash_context_t *const ctx,
                                   hash_mode_t hash_mode);

/**
 * Performs the UPDATE operation for a cryptographic hash function.
 *
 * The update operation processes the `input_message` using the selected
 * hash compression function. The intermediate digest is stored in the
 * context `ctx`. Any partial data is stored back in the context and
 * combined with the subsequent bytes.
 *
 * #otcrypto_hash_init should be called before this function.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t Result of the hash update operation
 */
crypto_status_t otcrypto_hash_update(hash_context_t *const ctx,
                                     crypto_const_uint8_buf_t input_message);

/**
 * Performs the FINAL operation for a cryptographic hash function.
 *
 * The final operation processes the remaining partial blocks,
 * computes the final hash and copies it to the `digest` parameter.
 *
 * #otcrypto_hash_update should be called before this function.
 *
 * The caller should allocate space for the `digest` buffer, (expected
 * length depends on `hash_mode`, refer table-1), and set the length
 * of expected output in the `len` field of `digest`. If the user-set
 * length and the output length does not match, an error message will
 * be returned.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t Result of the hash final operation
 */
crypto_status_t otcrypto_hash_final(hash_context_t *const ctx,
                                    crypto_uint8_buf_t *digest);

/**
 * Performs the HMAC / KMAC function on the input data.
 *
 * HMAC: This function computes the required MAC function on the
 * `input_message` using the `key` and returns a `digest`.
 *
 * KMAC: This function computes the KMAC on the `input_message` using
 * the `key` and returns a `digest` of `required_output_len`. The
 * customization string is passed through `customization_string`
 * parameter. If no customization is desired it can be empty. The
 * `customization_string` and `required_output_len` is only used for
 * KMAC modes and is ignored for the HMAC mode.
 *
 * The caller should allocate space for the `digest` buffer, (expected
 * length is 32 bytes for HMAC and `required_output_len`for KMAC), and
 * set the length of expected output in the `len` field of `digest`.
 * If the user-set length and the output length does not match, an
 * error message will be returned.
 *
 * @param key Pointer to the blinded key struct with key shares
 * @param input_message Input message to be hashed
 * @param mac_mode Required operation to be performed (HMAC/KMAC)
 * @param customization_string Customization string for KMAC
 * @param required_output_len Required output length from KMAC, in
 * bytes
 * @param digest Output digest after hashing the input data
 * @return crypto_status_t The result of the KMAC128 operation
 */
crypto_status_t otcrypto_mac(const crypto_blinded_key_t *key,
                             crypto_const_uint8_buf_t input_message,
                             mac_mode_t mac_mode,
                             crypto_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *digest);

/**
 * Performs the INIT operation for HMAC.
 *
 * Initializes the generic HMAC context. The required HMAC mode is
 * selected through the `hmac_mode` parameter. Populates the HMAC
 * context with the digest size, block size, HMAC update and HMAC
 * final APIs to be called based on the mode.
 *
 * The structure of HMAC context and how it populates the required
 * fields based on the HMAC mode are internal to the specific HMAC
 * implementation.
 *
 * The HMAC streaming API supports only the `kMacModeHmacSha256` mode.
 * Other modes are not supported and an error would be returned. The
 * interface is designed to be generic to support other required modes
 * in the future.
 *
 * @param ctx Pointer to the generic HMAC context struct
 * @param key Pointer to the blinded HMAC key struct
 * @param hmac_mode Required HMAC mode
 * @return crypto_status_t Result of the HMAC init operation
 */
crypto_status_t otcrypto_hmac_init(hmac_context_t *ctx,
                                   const crypto_blinded_key_t *key,
                                   mac_mode_t hmac_mode);

/**
 * Performs the UPDATE operation for HMAC.
 *
 * The update operation processes the `input_message` using the selected
 * compression function. The intermediate digest is stored in the HMAC
 * context `ctx`. Any partial data is stored back in the context and
 * combined with the subsequent bytes.
 *
 * #otcrypto_hmac_init should be called before calling this function.
 *
 * @param ctx Pointer to the generic HMAC context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t Result of the HMAC update operation
 */
crypto_status_t otcrypto_hmac_update(hmac_context_t *const ctx,
                                     crypto_const_uint8_buf_t input_message);

/**
 * Performs the FINAL operation for HMAC.
 *
 * The final operation processes the remaining partial blocks,
 * computes the final digest and copies it to the `digest` parameter.
 *
 * #otcrypto_hmac_update should be called before calling this function.
 *
 * The caller should allocate space for the `digest` buffer, (expected
 * length is 32 bytes for HMAC), and set the length of expected output
 * in the `len` field of `digest`. If the user-set length and the
 * output length does not match, an error message will be returned.
 *
 * @param ctx Pointer to the generic HMAC context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t Result of the HMAC final operation
 */
crypto_status_t otcrypto_hmac_final(hmac_context_t *const ctx,
                                    crypto_uint8_buf_t *digest);

/**
 * Performs the RSA key generation.
 *
 * Computes RSA private key (d) and RSA public key exponent (e) and
 * modulus (n).
 *
 * @param required_key_len Requested key length
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @return crypto_status_t Result of the RSA key generation
 */
crypto_status_t otcrypto_rsa_keygen(rsa_key_size_t required_key_len,
                                    rsa_public_key_t *rsa_public_key,
                                    rsa_private_key_t *rsa_private_key);

/**
 * Computes the digital signature on the input message data.
 *
 * The caller should allocate space for the `signature` buffer,
 * (expected length same as modulus length from `rsa_private_key`),
 * and set the length of expected output in the `len` field of
 * `signature`. If the user-set length and the output length does not
 * match, an error message will be returned.
 *
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @param input_message Input message to be signed
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to generated signature struct
 * @return crypto_status_t The result of the RSA sign generation
 */
crypto_status_t otcrypto_rsa_sign(const rsa_private_key_t *rsa_private_key,
                                  crypto_const_uint8_buf_t input_message,
                                  rsa_padding_t padding_mode,
                                  rsa_hash_t hash_mode,
                                  crypto_uint8_buf_t *signature);

/**
 * Verifies the authenticity of the input signature.
 *
 * The generated signature is compared against the input signature and
 * PASS / FAIL is returned.
 *
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param input_message Input message to be signed for verification
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to the input signature to be verified
 * @param verification_result Returns the result of signature
 * verification (Pass/Fail)
 * @return crypto_status_t The status of the RSA verify operation
 */
crypto_status_t otcrypto_rsa_verify(const rsa_public_key_t *rsa_public_key,
                                    crypto_const_uint8_buf_t input_message,
                                    rsa_padding_t padding_mode,
                                    rsa_hash_t hash_mode,
                                    crypto_const_uint8_buf_t signature,
                                    verification_status_t *verification_result);

/**
 * Performs the key generation for ECDSA operation.
 *
 * Computes private key (d) and public key (Q) keys for ECDSA
 * operation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @param private_key Pointer to the blinded private key (d) struct
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @return crypto_status_t Result of the ECDSA key generation
 */
crypto_status_t otcrypto_ecdsa_keygen(ecc_curve_t *elliptic_curve,
                                      crypto_blinded_key_t *private_key,
                                      ecc_public_key_t *public_key);

/**
 * Performs the ECDSA digital signature generation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param input_message Input message to be signed
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @param signature Pointer to the signature struct with (r,s) values
 * @return crypto_status_t Result of the ECDSA signature generation
 */
crypto_status_t otcrypto_ecdsa_sign(const crypto_blinded_key_t *private_key,
                                    crypto_const_uint8_buf_t input_message,
                                    ecc_curve_t *elliptic_curve,
                                    ecc_signature_t *signature);

/**
 * Performs the deterministic ECDSA digital signature generation.
 *
 * In the case of deterministic ECDSA, the random value ‘k’ for the
 * signature generation is deterministically generated from the
 * private key and the input message. Refer to RFC6979 for details.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param input_message Input message to be signed
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @param signature Pointer to the signature struct with (r,s) values
 * @return crypto_status_t Result of the deterministic ECDSA signature
 * generation
 */
crypto_status_t otcrypto_deterministic_ecdsa_sign(
    const crypto_blinded_key_t *private_key,
    crypto_const_uint8_buf_t input_message, ecc_curve_t *elliptic_curve,
    ecc_signature_t *signature);

/**
 * Performs the ECDSA digital signature verification.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @param input_message Input message to be signed for verification
 * @param signature Pointer to the signature to be verified
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @param verification_result Result of verification (Pass/Fail)
 * @return crypto_status_t Result of the ECDSA verification operation
 */
crypto_status_t otcrypto_ecdsa_verify(
    const ecc_public_key_t *public_key, crypto_const_uint8_buf_t input_message,
    ecc_signature_t *signature, ecc_curve_t *elliptic_curve,
    verification_status_t *verification_result);

/**
 * Performs the key generation for ECDH key agreement.
 *
 * Computes private key (d) and public key (Q) keys for ECDSA
 * operation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @param private_key Pointer to the blinded private key (d) struct
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @return crypto_status_t Result of the ECDH key generation
 */
crypto_status_t otcrypto_ecdh_keygen(ecc_curve_t *elliptic_curve,
                                     crypto_blinded_key_t *private_key,
                                     ecc_public_key_t *public_key);

/**
 * Performs Elliptic Curve Diffie Hellman shared secret generation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @param shared_secret Pointer to generated blinded shared key struct
 * @return crypto_status_t Result of ECDH shared secret generation
 */
crypto_status_t otcrypto_ecdh(const crypto_blinded_key_t *private_key,
                              const ecc_public_key_t *public_key,
                              ecc_curve_t *elliptic_curve,
                              crypto_blinded_key_t *shared_secret);

/**
 * Generates a new Ed25519 key pair.
 *
 * Computes the private exponent (d) and public key (Q) based on
 * Curve25519.
 *
 * No domain_parameter is needed and is automatically set for Ed25519.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param public_key Pointer to the unblinded public key struct
 * @return crypto_status_t Result of the Ed25519 key generation
 */
crypto_status_t otcrypto_ed25519_keygen(crypto_blinded_key_t *private_key,
                                        crypto_unblinded_key_t *public_key);

/**
 * Generates an Ed25519 digital signature.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param input_message Input message to be signed
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode
 * @param signature Pointer to the EdDSA signature with (r,s) values
 * @return crypto_status_t Result of the EdDSA signature generation
 */
crypto_status_t otcrypto_ed25519_sign(const crypto_blinded_key_t *private_key,
                                      crypto_const_uint8_buf_t input_message,
                                      eddsa_sign_mode_t sign_mode,
                                      ecc_signature_t *signature);

/**
 * Verifies an Ed25519 signature.
 *
 * @param public_key Pointer to the unblinded public key struct
 * @param input_message Input message to be signed for verification
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature
 * verification (Pass/Fail)
 * @return crypto_status_t Result of the EdDSA verification operation
 */
crypto_status_t otcrypto_ed25519_verify(
    const crypto_unblinded_key_t *public_key,
    crypto_const_uint8_buf_t input_message, eddsa_sign_mode_t sign_mode,
    ecc_signature_t *signature, verification_status_t *verification_result);

/**
 * Generates a new key pair for X25519 key exchange.
 *
 * Computes the private scalar (d) and public key (Q) based on
 * Curve25519.
 *
 * No domain_parameter is needed and is automatically set for X25519.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param public_key Pointer to the unblinded public key struct
 * @return crypto_status_t Result of the X25519 key generation
 */
crypto_status_t otcrypto_x25519_keygen(crypto_blinded_key_t *private_key,
                                       crypto_unblinded_key_t *public_key);

/**
 * Performs the X25519 Diffie Hellman shared secret generation.
 *
 * @param private_key Pointer to blinded private key (u-coordinate)
 * @param public_key Pointer to the public scalar from the sender
 * @param shared_secret Pointer to shared secret key (u-coordinate)
 * @return crypto_status_t Result of the X25519 operation
 */
crypto_status_t otcrypto_x25519(const crypto_blinded_key_t *private_key,
                                const crypto_unblinded_key_t *public_key,
                                crypto_blinded_key_t *shared_secret);

/**
 * Starts the asynchronous RSA key generation function.
 *
 * Initializes OTBN and starts the OTBN routine to compute the RSA
 * private key (d), RSA public key exponent (e) and modulus (n).
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param required_key_len Requested key length
 * @return crypto_status_t Result of async RSA keygen start operation
 */
crypto_status_t otcrypto_rsa_keygen_async_start(
    rsa_key_size_t required_key_len);

/**
 * Finalizes the asynchronous RSA key generation function.
 *
 * Returns `kCryptoStatusOK` and copies the RSA private key (d), RSA
 * public key exponent (e) and modulus (n) if the OTBN status is done,
 * or `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @return crypto_status_t Result of asynchronous RSA keygen finalize
 * operation
 */
crypto_status_t otcrypto_rsa_keygen_async_finalize(
    rsa_public_key_t *rsa_public_key, rsa_private_key_t *rsa_private_key);

/**
 * Starts the asynchronous digital signature generation function.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message.
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param rsa_private_key Pointer to RSA private exponent struct
 * @param input_message Input message to be signed
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @return crypto_status_t Result of async RSA sign start operation
 */
crypto_status_t otcrypto_rsa_sign_async_start(
    const rsa_private_key_t *rsa_private_key,
    crypto_const_uint8_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode);

/**
 * Finalizes the asynchronous digital signature generation function.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * The caller should allocate space for the `signature` buffer,
 * (expected length same as modulus length from `rsa_private_key`),
 * and set the length of expected output in the `len` field of
 * `signature`. If the user-set length and the output length does not
 * match, an error message will be returned.
 *
 * @param signature Pointer to generated signature struct
 * @return crypto_status_t Result of async RSA sign finalize operation
 */
crypto_status_t otcrypto_rsa_sign_async_finalize(crypto_uint8_buf_t *signature);

/**
 * Starts the asynchronous signature verification function.
 *
 * Initializes OTBN and starts the OTBN routine to recover the message
 * from the input signature.
 *
 * @param rsa_public_key Pointer to RSA public exponent struct
 * @param signature Pointer to the input signature to be verified
 * @return crypto_status_t Result of async RSA verify start operation
 */
crypto_status_t otcrypto_rsa_verify_async_start(
    const rsa_public_key_t *rsa_public_key, crypto_const_uint8_buf_t signature);

/**
 * Finalizes the asynchronous signature verification function.
 *
 * Returns `kCryptoStatusOK` and populates the `verification result`
 * if the OTBN status is done, or `kCryptoStatusAsyncIncomplete` if
 * OTBN is busy or `kCryptoStatusInternalError` if there is an error.
 * The (hash of) recovered message is compared against the input
 * message and a PASS or FAIL is returned.
 *
 * @param input_message Input message to be signed for verification
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param verification_result Returns the result of verification
 * @return crypto_status_t Result of async RSA verify finalize
 * operation
 */
crypto_status_t otcrypto_rsa_verify_async_finalize(
    crypto_const_uint8_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode, verification_status_t *verification_result);

/**
 * Starts the asynchronous key generation for ECDSA operation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the private
 * key (d) and public key (Q) for ECDSA operation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @return crypto_status_t Result of asynchronous ECDSA keygen start
 * operation.
 */
crypto_status_t otcrypto_ecdsa_keygen_async_start(ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous key generation for ECDSA operation.
 *
 * Returns `kCryptoStatusOK` and copies the private key (d) and public
 * key (Q), if the OTBN status is done, or
 * `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @return crypto_status_t Result of asynchronous ECDSA keygen
 * finalize operation
 */
crypto_status_t otcrypto_ecdsa_keygen_async_finalize(
    crypto_blinded_key_t *private_key, ecc_public_key_t *public_key);

/**
 * Starts the asynchronous ECDSA digital signature generation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message. The domain_parameter field of the
 * `elliptic_curve` is required only for a custom curve. For named
 * curves this field is ignored and can be set to NULL.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param input_message Input message to be signed
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @return crypto_status_t Result of async ECDSA start operation
 */
crypto_status_t otcrypto_ecdsa_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_uint8_buf_t input_message, ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous ECDSA digital signature generation.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param signature Pointer to the signature struct with (r,s) values
 * @return crypto_status_t Result of async ECDSA finalize operation
 */
crypto_status_t otcrypto_ecdsa_sign_async_finalize(ecc_signature_t *signature);

/**
 * Starts the asynchronous deterministic ECDSA digital signature generation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message. The domain_parameter field of the
 * `elliptic_curve` is required only for a custom curve. For named
 * curves this field is ignored and can be set to NULL.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param input_message Input message to be signed
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @return crypto_status_t Result of async ECDSA start operation
 */
crypto_status_t otcrypto_deterministic_ecdsa_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_uint8_buf_t input_message, ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous deterministic ECDSA digital signature generation.
 *
 * In the case of deterministic ECDSA, the random value ‘k’ for the
 * signature generation is deterministically generated from the
 * private key and the input message. Refer to RFC6979 for details.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param signature Pointer to the signature struct with (r,s) values
 * @return crypto_status_t Result of async deterministic ECDSA finalize
 * operation
 */
crypto_status_t otcrypto_ecdsa_deterministic_sign_async_finalize(
    ecc_signature_t *signature);

/**
 * Starts the asynchronous ECDSA digital signature verification.
 *
 * Initializes OTBN and starts the OTBN routine to recover ‘r’ value
 * from the input signature ‘s’ value. The domain_parameter field of
 * `elliptic_curve` is required only for a custom curve. For named
 * curves this field is ignored and can be set to NULL.
 *
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @param input_message Input message to be signed for verification
 * @param signature Pointer to the signature to be verified
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @return crypto_status_t Result of async ECDSA verify start function
 */
crypto_status_t otcrypto_ecdsa_verify_async_start(
    const ecc_public_key_t *public_key, crypto_const_uint8_buf_t input_message,
    ecc_signature_t *signature, ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous ECDSA digital signature verification.
 *
 * Returns `kCryptoStatusOK` and populates the `verification result`
 * if the OTBN status is done. `kCryptoStatusAsyncIncomplete` if the
 * OTBN is busy or `kCryptoStatusInternalError` if there is an error.
 * The computed signature is compared against the input signature
 * and a PASS or FAIL is returned.
 *
 * @param verification_result Returns the result of verification
 * @return crypto_status_t Result of async ECDSA verify finalize
 * operation
 */
crypto_status_t otcrypto_ecdsa_verify_async_finalize(
    verification_status_t *verification_result);

/**
 * Starts the asynchronous key generation for ECDH operation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the private
 * key (d) and public key (Q) for ECDH operation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * Returns `kCryptoStatusOK` if the operation was successfully
 * started, or`kCryptoStatusInternalError` if the operation cannot be
 * started.
 *
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @return crypto_status_t Result of asynchronous ECDH keygen start
 * operation.
 */
crypto_status_t otcrypto_ecdh_keygen_async_start(ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous key generation for ECDSA operation.
 *
 * Returns `kCryptoStatusOK` and copies the private key (d) and public
 * key (Q), if the OTBN status is done, or
 * `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @return crypto_status_t Result of asynchronous ECDH keygen
 * finalize operation
 */
crypto_status_t otcrypto_ecdh_keygen_async_finalize(
    crypto_blinded_key_t *private_key, ecc_public_key_t *public_key);

/**
 * Starts the asynchronous Elliptic Curve Diffie Hellman shared
 * secret generation.
 *
 * The domain_parameter field of the `elliptic_curve` is required
 * only for a custom curve. For named curves this field is ignored
 * and can be set to NULL.
 *
 * @param private_key Pointer to the blinded private key (d) struct
 * @param public_key Pointer to the unblinded public key (Q) struct
 * @param elliptic_curve Pointer to the elliptic curve to be used
 * @return crypto_status_t Result of async ECDH start operation
 */
crypto_status_t otcrypto_ecdh_async_start(
    const crypto_blinded_key_t *private_key, const ecc_public_key_t *public_key,
    ecc_curve_t *elliptic_curve);

/**
 * Finalizes the asynchronous Elliptic Curve Diffie Hellman shared
 * secret generation.
 *
 * Returns `kCryptoStatusOK` and copies `shared_secret` if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN
 * is busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param shared_secret Pointer to generated blinded shared key struct
 * @return crypto_status_t Result of async ECDH finalize operation
 */
crypto_status_t otcrypto_ecdh_async_finalize(
    crypto_blinded_key_t *shared_secret);

/**
 * Starts the asynchronous key generation for Ed25519.
 *
 * Initializes OTBN and starts the OTBN routine to compute the private
 * exponent (d) and public key (Q) based on Curve25519.
 *
 * No domain_parameter is needed and is automatically set for X25519.
 *
 * @return crypto_status_t Result of asynchronous ed25519 keygen start
 * operation.
 */
crypto_status_t otcrypto_ed25519_keygen_async_start();

/**
 * Finalizes the asynchronous key generation for Ed25519.
 *
 * Returns `kCryptoStatusOK` and copies private key (d) and public key
 * (Q), if the OTBN status is done, or `kCryptoStatusAsyncIncomplete`
 * if the OTBN is busy or `kCryptoStatusInternalError` if there is an
 * error.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param public_key Pointer to the unblinded public key struct
 * @return crypto_status_t Result of asynchronous ed25519 keygen
 * finalize operation.
 */
crypto_status_t otcrypto_ed25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous Ed25519 digital signature generation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message. The domain_parameter field for
 * Ed25519 is automatically set.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param input_message Input message to be signed
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode
 * @param signature Pointer to the EdDSA signature to get (r) value
 * @return crypto_status_t Result of async Ed25519 start operation
 */
crypto_status_t otcrypto_ed25519_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_uint8_buf_t input_message, eddsa_sign_mode_t sign_mode,
    ecc_signature_t *signature);

/**
 * Finalizes the asynchronous Ed25519 digital signature generation.
 *
 * Returns `kCryptoStatusOK` and copies the signature if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN is
 * busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param signature Pointer to the EdDSA signature to get (s) value
 * @return crypto_status_t Result of async Ed25519 finalize operation
 */
crypto_status_t otcrypto_ed25519_sign_async_finalize(
    ecc_signature_t *signature);

/**
 * Starts the asynchronous Ed25519 digital signature verification.
 *
 * Initializes OTBN and starts the OTBN routine to verify the
 * signature. The domain_parameter for Ed25519 is set automatically.
 *
 * @param public_key Pointer to the unblinded public key struct
 * @param input_message Input message to be signed for verification
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature
 * verification (Pass/Fail)
 * @return crypto_status_t Result of async Ed25519 verification start
 * function
 */
crypto_status_t otcrypto_ed25519_verify_async_start(
    const crypto_unblinded_key_t *public_key,
    crypto_const_uint8_buf_t input_message, eddsa_sign_mode_t sign_mode,
    ecc_signature_t *signature);

/**
 * Finalizes the asynchronous Ed25519 digital signature verification.
 *
 * Returns `kCryptoStatusOK` and populates the `verification result`
 * with a PASS or FAIL, if the OTBN status is done,
 * `kCryptoStatusAsyncIncomplete` if the OTBN is busy or
 * `kCryptoStatusInternalError` if there is an error.
 *
 * @param verification_result Returns the result of verification
 * @return crypto_status_t Result of async Ed25519 verification
 * finalize function
 */
crypto_status_t otcrypto_ed25519_verify_async_finalize(
    verification_status_t *verification_result);

/**
 * Starts the asynchronous key generation for X25519.
 *
 * Initializes OTBN and starts the OTBN routine to compute the private
 * exponent (d) and public key (Q) based on Curve25519.
 *
 * No domain_parameter is needed and is automatically set for X25519.
 *
 * @return crypto_status_t Result of asynchronous X25519 keygen start
 * operation.
 */
crypto_status_t otcrypto_x25519_keygen_async_start();

/**
 * Finalizes the asynchronous key generation for X25519.
 *
 * Returns `kCryptoStatusOK` and copies private key (d) and public key
 * (Q), if the OTBN status is done, or `kCryptoStatusAsyncIncomplete`
 * if the OTBN is busy or `kCryptoStatusInternalError` if there is an
 * error.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param public_key Pointer to the unblinded public key struct
 * @return crypto_status_t Result of asynchronous X25519 keygen
 * finalize operation.
 */
crypto_status_t otcrypto_x25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous X25519 Diffie Hellman shared secret
 * generation.
 *
 * Initializes OTBN and starts the OTBN routine to perform Diffie
 * Hellman shared secret generation based on Curve25519. The
 * domain parameter is automatically set for X25519 API.
 *
 * @param private_key Pointer to the blinded private key
 * (u-coordinate)
 * @param public_key Pointer to the public scalar from the sender
 * @return crypto_status_t Result of the async X25519 start operation
 */
crypto_status_t otcrypto_x25519_async_start(
    const crypto_blinded_key_t *private_key,
    const crypto_unblinded_key_t *public_key);

/**
 * Finalizes the asynchronous X25519 Diffie Hellman shared secret
 * generation.
 *
 * Returns `kCryptoStatusOK` and copies `shared_secret` if the OTBN
 * status is done, or `kCryptoStatusAsyncIncomplete` if the OTBN
 * is busy or `kCryptoStatusInternalError` if there is an error.
 *
 * @param shared_secret Pointer to shared secret key (u-coordinate)
 * @return crypto_status_t Result of async X25519 finalize operation
 */
crypto_status_t otcrypto_x25519_async_finalize(
    crypto_blinded_key_t *shared_secret);

/**
 * Instantiates the DRBG system.
 *
 * Initializes the DRBG and the context for DRBG. Gets the required
 * entropy input automatically from the entropy source.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param nonce Pointer to the nonce bit-string
 * @param perso_string Pointer to personalization bitstring
 * @return crypto_status_t Result of the DRBG instantiate operation
 */
crypto_status_t otcrypto_drbg_instantiate(drbg_state_t *drbg_state,
                                          crypto_uint8_buf_t nonce,
                                          crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with fresh entropy that is automatically fetched
 * from the entropy source and updates the working state parameters.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param additional_input Pointer to the additional input for DRBG
 * @return crypto_status_t Result of the DRBG reseed operation
 */
crypto_status_t otcrypto_drbg_reseed(drbg_state_t *drbg_state,
                                     crypto_uint8_buf_t additional_input);

/**
 * Instantiates the DRBG system.
 *
 * Initializes DRBG and the DRBG context. Gets the required entropy
 * input from the user through the `entropy` parameter.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param entropy Pointer to the user defined entropy value
 * @param nonce Pointer to the nonce bit-string
 * @param personalization_string Pointer to personalization bitstring
 * @return crypto_status_t Result of the DRBG manual instantiation
 */
crypto_status_t otcrypto_drbg_manual_instantiate(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t nonce, crypto_uint8_buf_t perso_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with entropy input from the user through `entropy`
 * parameter and updates the working state parameters.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param entropy Pointer to the user defined entropy value
 * @param additional_input Pointer to the additional input for DRBG
 * @return crypto_status_t Result of the manual DRBG reseed operation
 */
crypto_status_t otcrypto_drbg_manual_reseed(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t additional_input);

/**
 * DRBG function for generating random bits.
 *
 * Used to generate pseudo random bits after DRBG instantiation or
 * DRBG reseeding.
 *
 * The caller should allocate space for the `drbg_output` buffer,
 * (of length `output_len`), and set the length of expected
 * output in the `len` field of `drbg_output`. If the user-set length
 * and the output length does not match, an error message will be
 * returned.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @param additional_input Pointer to the additional data
 * @param output_len Required len of pseudorandom output, in bytes
 * @param drbg_output Pointer to the generated pseudo random bits
 * @return crypto_status_t Result of the DRBG generate operation
 */
crypto_status_t otcrypto_drbg_generate(drbg_state_t *drbg_state,
                                       crypto_uint8_buf_t additional_input,
                                       size_t output_len,
                                       crypto_uint8_buf_t *drbg_output);

/**
 * Uninstantiates DRBG and clears the context.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @return crypto_status_t Result of the DRBG uninstantiate operation
 */
crypto_status_t otcrypto_drbg_uninstantiate(drbg_state_t *drbg_state);

/**
 * Performs the key derivation function in counter mode.
 *
 * The required PRF engine for the KDF function is selected using the
 * `kdf_mode` parameter.
 *
 * @param key_derivation_key Pointer to the blinded key derivation key
 * @param kdf_mode Required KDF mode, with HMAC or KMAC as a PRF
 * @param key_mode Crypto mode for which the derived key is intended
 * @param required_bit_len Required length of the derived key in bits
 * @param keying_material Pointer to the blinded keying material
 * @return crypto_status_t Result of the key derivation operation
 */
crypto_status_t otcrypto_kdf_ctr(const crypto_blinded_key_t key_derivation_key,
                                 kdf_type_t kdf_mode, key_mode_t key_mode,
                                 size_t required_bit_len,
                                 crypto_blinded_key_t keying_material);

/**
 * Builds an unblinded key struct from a user (plain) key.
 *
 * @param plain_key Pointer to the user defined plain key
 * @param key_mode Crypto mode for which the key usage is intended
 * @param unblinded_key Generated unblinded key struct
 * @return crypto_status_t Result of the build unblinded key operation
 */
crypto_status_t otcrypto_build_unblinded_key(
    crypto_const_uint8_buf_t plain_key, key_mode_t key_mode,
    crypto_unblinded_key_t unblinded_key);

/**
 * Builds a blinded key struct from a plain key.
 *
 * This API takes as input a plain key from the user and masks
 * it using an implantation specific masking with ‘n’ shares and
 * generates a blinded key struct as output.
 *
 * @param plain_key Pointer to the user defined plain key
 * @param key_mode Crypto mode for which the key usage is intended
 * @param blinded_key Generated blinded key struct
 * @return crypto_status_t Result of the build blinded key operation
 */
crypto_status_t otcrypto_build_blinded_key(crypto_const_uint8_buf_t plain_key,
                                           key_mode_t key_mode,
                                           crypto_blinded_key_t blinded_key);

/**
 * Exports the blinded key struct to an unblinded key struct.
 *
 * This API takes as input a blinded key masked with ‘n’ shares, and
 * removes the masking and generates an unblinded key struct as output.
 *
 * @param blinded_key Blinded key struct to be unmasked
 * @param unblinded_key Generated unblinded key struct
 * @return crypto_status_t Result of the blinded key export operation
 */
crypto_status_t otcrypto_blinded_to_unblinded_key(
    const crypto_blinded_key_t blinded_key,
    crypto_unblinded_key_t unblinded_key);

/**
 * Build a blinded key struct from an unblinded key struct.
 *
 * @param unblinded_key Blinded key struct to be unmasked
 * @param blinded_key Generated (unmasked) unblinded key struct
 * @return crypto_status_t Result of unblinded key export operation
 */
crypto_status_t otcrypto_unblinded_to_blinded_key(
    const crypto_unblinded_key unblinded_key, crypto_blinded_key_t blinded_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
