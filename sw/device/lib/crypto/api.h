// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_API_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_API_H_

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enum to handle return values of the crypto API.
 */
typedef enum crypto_status {
  // Status is OK; no errors.
  kCryptoStatusOK = 0x7d3a,
  // Invalid input arguments; Wrong length or invalid type.
  kCryptoIncorrectInput = 0x6b7f,
  // Inconsistencies when cross-checking results, witness, checksums.
  kCryptoStatusInternalError = 0x4753,
  // An asynchronous operation is still in progress.
  kCryptoStatusAsyncIncomplete = 0xe2b7
} crypto_status_t;

/**
 * Enum to handle return values of the verification APIs.
 */
typedef enum verification_status {
  // Return value for successful verification.
  kVerificationStatusPass = 0x2c89,
  // Return value for unsuccessful verification.
  kVerificationStatusFail = 0x49d3
} verification_status_t;

/**
 * Enum for opentitan crypto modes using a key.
 *
 * Used to denote crypto mode for which key usage is intended.
 */
typedef enum key_mode {
  // AES ECB mode.
  kKeyModeAesEcb = 0x0101,
  // AES CBC mode.
  kKeyModeAesCbc = 0x0102,
  // AES CFB mode.
  kKeyModeAesCfb = 0x0103,
  // AES OFB mode.
  kKeyModeAesOfb = 0x0104,
  // AES CTR mode.
  kKeyModeAesCtr = 0x0105,
  // AES GCM mode.
  kKeyModeAesGcm = 0x0106,
  // AES KWP mode.
  kKeyModeAesKwp = 0x0107,
  // HMAC-SHA-256.
  kKeyModeHmacSha256 = 0x0201,
  // KMAC-256.
  kKeyModeKmac256 = 0x0202,
  // RSA key generation.
  kKeyModeRsaKeygen = 0x0301,
  // RSA digital signature.
  kKeyModeRsaSign = 0x0302,
  // Elliptic curve key generation.
  kKeyModeEccKeygen = 0x0401,
  // Elliptic curve digital signature.
  kKeyModeEccSign = 0x0402,
  // Elliptic curve Diffie–Hellman key exchange.
  kKeyModeEccEcdh = 0x0403
} key_mode_t;

/**
 * Type of blinded keys.
 *
 * This type is not exposed in the API because it should not be used directly.
 */
extern struct crypto_blinded_key_t;

/**
 * Struct to handle unmasked key type.
 */
typedef struct crypto_unblinded_key {
  // Mode for which the key usage is intended.
  key_mode_t key_mode;
  // Key length.
  uint16_t key_length;
  // Implementation specific, storage provided by caller.
  uint32_t *key;
  // Checksum for this struct.
  uint32_t checksum;
} crypto_unblinded_key_t;

/**
 * Enum to define AES mode of operation.
 */
typedef enum block_cipher_mode {
  // AES ECB mode (electronic codebook mode).
  kBlockCipherModeEcb = 0,
  // AES CBC mode (cipher block chaining mode).
  kBlockCipherModeCbc = 1,
  // AES CFB mode (cipher feedback mode).
  kBlockCipherModeCfb = 2,
  // AES OFB mode (output feedback mode).
  kBlockCipherModeOfb = 3,
  // AES CTR mode (counter mode).
  kBlockCipherModeCtr = 4
} block_cipher_mode_t;

/**
 * Enum to define AES operation to be performed.
 */
typedef enum aes_operation {
  // AES operation mode encrypt.
  kAesOperationEncrypt = 0,
  // AES operation mode decrypt.
  kAesOperationDecrypt = 1
} aes_operation_t;

/**
 * Enum to define padding scheme for AES data.
 */
typedef enum aes_padding {
  // Pads with value same as the number of padding bytes.
  kAesPaddingPkcs7 = 0,
  // Pads with 0x80 (10000000), followed by zero bytes.
  kAesPaddingIso9797M2 = 1,
  // Pads with 0x00 bytes.
  kAesPaddingIso9797M1 = 2,
  // Pads with random bytes, last byte is no. of padded bytes.
  kAesPaddingRandom = 3,
  // Pads with 0x00 bytes, last byte is no. of padded bytes.
  kAesPaddingX923 = 4,
  // Add no padding.
  kAesPaddingNull = 5
} aes_padding_t;

/**
 * Enum to define hashing mode.
 */
typedef enum hash_mode {
  // SHA2-256 mode.
  kHashModeSha256 = 0,
  // SHA2-384 mode.
  kHashModeSha384 = 1,
  // SHA2-512 mode.
  kHashModeSha512 = 2,
  // SHA3-224 mode.
  kHashModeSha3_224 = 3,
  // SHA3-256 mode.
  kHashModeSha3_256 = 4,
  // SHA3-384 mode.
  kHashModeSha3_384 = 5,
  // SHA3-512 mode.
  kHashModeSha3_512 = 6,
  // SHA3-Shake128 mode.
  kHashModeSha3Shake128 = 7,
  // SHA3-Shake256 mode.
  kHashModeSha3Shake256 = 8,
  // SHA3-cShake128 mode.
  kHashModeSha3Cshake128 = 9,
  // SHA3-cShake256 mode.
  kHashModeSha3Cshake256 = 10
} hash_mode_t;

/**
 * Enum to define MAC mode.
 */
typedef enum mac_mode {
  // HMAC-SHA2-256 mode.
  kMacModeHmacSha256 = 0,
  // KMAC-128 mode.
  kMacModeKmac128 = 1,
  // KMAC-256 mode.
  kMacModeKmac256 = 2
} mac_mode_t;

/**
 * Enum to define padding scheme for RSA data.
 */
typedef enum rsa_padding {
  // Pads input data according to the PKCS#1-OAEP scheme.
  kRsaPaddingOaep = 0,
  // Pads input data according to the PKCS#1 (v1.5) scheme.
  kRsaPaddingPkcs = 1,
  // Pads input data according to the PKCS#1-PSS scheme.
  kRsaPaddingPss = 2,
  // NULL padding.
  kRsaPaddingNull = 3
} rsa_padding_t;

/**
 * Enum to define hash modes for RSA scheme
 *
 * Aligning with existing HASH modes.
 */
typedef enum rsa_hash {
  // SHA2-256 hashing mode for RSA.
  kRsaHashSha256 = 0,
  // SHA2-384 hashing mode for RSA.
  kRsaHashSha384 = 1,
  // SHA2-512 hashing mode for RSA.
  kRsaHashSha512 = 2,
  // SHA3-384 hashing mode for RSA.
  kRsaHashSha3_384 = 3
} rsa_hash_t;

/**
 * Enum to define named elliptic curves.
 */
typedef enum ecc_named_curve {
  // ECC named curve NIST P256.
  kEccNamedCurveNistP256 = 0,
  // ECC named curve NIST P384.
  kEccNamedCurveNistP384 = 1,
  // ECC named curve brainpool P256r1.
  kEccNamedCurveBrainpoolP256R1 = 2
} ecc_named_curve_t;

/**
 * Struct to handle ECDSA result.
 */
typedef struct ecc_signature {
  // Length of ECC signature R parameter, in bytes.
  size_t signature_r_len;
  // ECC signature R parameter.
  uint32_t *signature_r;
  // Length of ECC signature S parameter, in bytes.
  size_t signature_s_len;
  // ECC signature S parameter.
  uint32_t *signature_s;
} ecc_signature_t;

/**
 * Enum to define EdDSA mode for signature.
 */
typedef enum eddsa_sign_mode {
  // Signature mode EdDSA.
  kEddsaSignModeEdDSA = 0,
  // Signature mode Hashed EdDSA.
  kEddsaSignModeHashEdDSA = 1
} eddsa_sign_mode_t;

/**
 * Struct to handle ECC public key type.
 *
 * Length of public key coordinates (x,y) follows len(prime_P).
 */
typedef struct ecc_public_key {
  // ECC public key x coordinate.
  uint32_t *pubKey_x;
  // ECC public key y coordinate.
  uint32_t *pubKey_y;
} ecc_public_key_t;

/**
 * Struct to handle EdDSA public key type.
 *
 * Length of encoded public key for ed25519 is 256 bits (32 bytes).
 */
typedef struct eddsa_public_key {
  // Public key for ed25519
  uint32_t *pubKey;
} eddsa_public_key_t;

/**
 * Struct for domain parameters for a generic ECC Weierstrass curve.
 */
typedef struct ecc_domain {
  // Length of prime P.
  size_t len_prime_P;
  // Value of prime P.
  uint32_t *prime_P;
  // Length of coefficient A.
  size_t len_A;
  // Value of coefficient A.
  uint32_t *A;
  // Length of coefficient B.
  size_t len_B;
  // Value of coefficient B.
  uint32_t *B;
  // Value of basepoint G’s x coordinate.
  uint32_t *base_point_G_x;
  // Value of basepoint G’s y coordinate.
  uint32_t *base_point_G_y;
  // Length of prime order of group.
  size_t len_prime_order_Q;
  // Value of prime order of group.
  uint32_t *prime_order_Q;
  // Cofactor of the curve.
  uint32_t cofactor;
  // Checksum value of the parameters.
  uint32_t checksum;
} ecc_domain_t;

/**
 * Struct to handle crypto data buffer with pointer and length.
 */
typedef struct crypto_uint8_buf {
  // Pointer to the data.
  uint8_t *data;
  // Length of the data in bytes.
  size_t len;
} crypto_uint8_buf_t;

/**
 * Performs the AES initialization operation.
 *
 * The `aes_mode`and `aes_operation` are selected and the `key`, `iv`
 * are loaded into the register.
 *
 * @param key Pointer to the blinded key struct with key shares
 * @param iv Initialization vector, used for CBC, CFB, OFB, CTR modes
 * @param aes_mode Required aes mode of operation
 * @param aes_operation Required aes operation
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t aes_init(const crypto_blinded_key_t *key, crypto_uint8_buf_t iv,
                         block_cipher_mode_t aes_mode,
                         aes_operation_t aes_operation);

/**
 * Performs the AES cipher operation.
 *
 * The #aes_init function should be called before this, to initialize
 * the key, aes mode and aes cipher operation to be performed.
 *
 * The input data in the `cipher_input` is first padded using the
 * aes_padding scheme, the output is placed in the `cipher_output`.
 *
 * @param cipher_input Input data to be ciphered
 * @param aes_padding Padding scheme to be used for the data
 * @param cipher_output Output data after cipher operation
 * @return crypto_status_t The result of the cipher operation
 */
crypto_status_t aes_cipher(const crypto_uint8_buf_t cipher_input,
                           aes_padding_t aes_padding,
                           crypto_uint8_buf_t *cipher_output);

/**
 * Performs the AES-GCM authenticated encryption operation.
 *
 * This function encrypts the input data `plaintext` to produce an
 * `ciphertext` output. Additionally it generates an authentication
 * tag `auth_tag` on both the (confidential) input data and any
 * additional non-confidential authenticated data `aad`.
 *
 * @param key Pointer to the blinded gcm-key struct
 * @param plaintext Input data to be encrypted and authenticated
 * @param iv Initialization vector for the encryption function
 * @param aad Additional authenticated data
 * @param ciphertext Encrypted output data, same length as input data
 * @param auth_tag Authentication tag
 * @return crypto_status_t The result of the encryption operation
 */
crypto_status_t aes_encrypt_gcm(const crypto_blinded_key_t *key,
                                const crypto_uint8_buf_t plaintext,
                                crypto_uint8_buf_t iv, crypto_uint8_buf_t aad,
                                crypto_uint8_buf_t *ciphertext,
                                crypto_uint8_buf_t *auth_tag);

/**
 * Performs the AES-GCM authenticated decryption operation.
 *
 * This function first verifies if the authentication tag `auth_tag`
 * matches the internally generated tag. Upon verification, the
 * function decrypts the input `ciphertext` to get a `plaintext data.
 *
 * @param key Pointer to the blinded gcm-key struct
 * @param ciphertext Input data to be decrypted
 * @param iv Initialization vector for the decryption function
 * @param aad Additional authenticated data
 * @param auth_tag Authentication tag to be verified
 * @param plaintext Decrypted plaintext data, same len as input data
 * @return crypto_status_t The result of the encryption operation
 */
crypto_status_t aes_decrypt_gcm(const crypto_blinded_key_t *key,
                                const crypto_uint8_buf_t ciphertext,
                                crypto_uint8_buf_t iv, crypto_uint8_buf_t aad,
                                crypto_uint8_buf_t auth_tag,
                                crypto_uint8_buf_t *plaintext);

/**
 * AES-GCM context.
 *
 * Representation is internal to the AES implementation; initialize with
 * #aes_gcm_init.
 */
extern struct aes_gcm_context_t;

/**
 * Initializes the AES-GCM engine.
 *
 * Generates the GHASH subkey H and pre-counter block J0 from the
 * `key` and `iv`, and stores them in the `gcm_context` struct.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param key Pointer to the blinded GCM key struct
 * @param iv Initialization vector for the GCM function
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t aes_gcm_init(aes_gcm_context_t *gcm_context,
                             const crypto_blinded_key_t *key,
                             crypto_uint8_buf_t iv);

/**
 * Updates the AAD value for the encryption/decryption function.
 *
 * After copying the aad, computes GHASH value and stores the result
 * in the `gcm_context` state parameter.
 *
 * #aes_gcm_init should be called before calling this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param aad Additional authenticated data
 * @return crypto_status_t The result of the aad update operation
 */
crypto_status_t aes_gcm_aad_update(aes_gcm_context_t *gcm_context,
                                   crypto_uint8_buf_t aad);

/**
 * Performs the AES-GCM authenticated encryption update operation.
 *
 * This function encrypts the input data in `plaintext` and produces
 * a `ciphertext` data as output. The partial data bytes are stored
 * back in the `gcm_context` partial_data parameter and combined with
 * subsequent bytes or padded to block length for the last block. The
 * intermediate result is stored in the `gcm_context` state parameter.
 *
 * #aes_gcm_init and if needed #aes_gcm_aad_update should be called
 * before calling this API.
 * @param gcm_context Pointer to the GCM context struct
 * @param plaintext Input data to be encrypted and authenticated
 * @param ciphertext Encrypted output data, same length as input data
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t aes_gcm_encrypt_update(aes_gcm_context_t *gcm_context,
                                       const crypto_uint8_buf_t plaintext,
                                       crypto_uint8_buf_t *ciphertext);

/**
 * Performs the AES-GCM authenticated encryption final operation.
 *
 * This function pads the remaining partial data and encrypts the
 * block. Computes GHASH of the updated state after and stores the
 * result back in `gcm_context` state parameter, for tag generation.
 *
 * #aes_gcm_encrypt_update should be called before calling this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param ciphertext Encrypted output data, same length as input data
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t aes_gcm_encrypt_final(aes_gcm_context_t *gcm_context,
                                      crypto_uint8_buf_t *ciphertext);

/**
 * Performs the authentication tag generation operation.
 *
 * Performs GCTR on the final state value stored in the `gcm_context`
 * and returns the generated `auth_tag`.
 *
 * #aes_gcm_encrypt_final should be called before using this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param auth_tag Authentication tag
 * @return crypto_status_t The result of the tag generate operation
 */
crypto_status_t aes_gcm_generate_tag(aes_gcm_context_t *gcm_context,
                                     crypto_uint8_buf_t *auth_tag);

/**
 * Performs the pre-step for AES-GCM tag verification operation.
 *
 * Note: Tag should be verified before decrypting ciphertext.
 *
 * This function computes the final state value from the `ciphertext`
 * and AAD data. The partial data bytes are stored back in the
 * `gcm_context` partial_data parameter. The intermediate result is
 * stored in the `gcm_context` state parameter.
 *
 * #aes_gcm_init and aes_gcm_aad_update should be called before using
 * this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param ciphertext Encrypted input data for tag generation
 * @return crypto_status_t The return status of the verify update operation
 */
crypto_status_t aes_gcm_verify_tag_update(aes_gcm_context_t *gcm_context,
                                          const crypto_uint8_buf_t ciphertext);

/**
 * Performs the AES-GCM tag verification operation.
 *
 * Note: Tag should be verified before decrypting ciphertext.
 *
 * This function pads the remaining partial data and after that
 * computes the authentication tag. The generated tag is verified
 * against the input `auth_tag` for correctness.
 *
 * #aes_gcm_verify_tag_update should be called before using this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param auth_tag Authentication tag
 * @param verification_result Result of the tag verification (Pass/Fail)
 * @return crypto_status_t The return status of the tag verify operation
 */
crypto_status_t aes_gcm_verify_tag_final(
    aes_gcm_context_t *gcm_context, crypto_uint8_buf_t auth_tag,
    verification_status_t *verification_result);

/**
 * Performs the AES-GCM decryption update operation.
 *
 * Note: Decrypt should only be used after Tag Verification.
 *
 * This function generates `plaintext` from the `ciphertext` data. The
 * partial data bytes are stored back in the `gcm_context`
 * partial_data parameter. The intermediate result is stored in the `
 * gcm_context` state parameter.
 *
 * #aes_gcm_init and aes_gcm_aad_update should be called before using
 * this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param ciphertext Input data to be decrypted
 * @param plaintext Decrypted plaintext data, same len as input data
 * @return crypto_status_t The result of the decrypt update operation
 */
crypto_status_t aes_gcm_decrypt_update(aes_gcm_context_t *gcm_context,
                                       const crypto_uint8_buf_t ciphertext,
                                       crypto_uint8_buf_t *plaintext);

/**
 * Performs the AES-GCM authenticated decryption final operation.
 *
 * This function pads the remaining partial data and decrypts the
 * block to `plaintext`.
 *
 * #aes_gcm_decrypt_update should be called before using this API.
 *
 * @param gcm_context Pointer to the GCM context struct
 * @param ciphertext Input data to be decrypted
 * @param plaintext Decrypted plaintext data, same len as input data
 * @return crypto_status_t The result of the decrypt operation
 */
crypto_status_t aes_gcm_decrypt_final(aes_gcm_context_t *gcm_context,
                                      crypto_uint8_buf_t *plaintext);

/**
 * Performs the AES-KWP authenticated encryption operation.
 *
 * This encrypt function takes an input key `key_to_wrap` and using
 * the encryption key `key_KEK` outputs a wrapped key `wrapped_key`.
 *
 * @param key_to_wrap Pointer to the blinded key to be wrapped
 * @param key_KEK Input Pointer to the blinded encryption key
 * @param wrapped_key Pointer to the output wrapped key
 * @return crypto_status_t The result of the aes-kwp encrypt operation
 */
crypto_status_t aes_kwp_encrypt(const crypto_blinded_key_t *key_to_wrap,
                                const crypto_blinded_key_t *key_KEK,
                                crypto_uint8_buf_t *wrapped_key);

/**
 * Performs the AES-KWP authenticated decryption operation.
 *
 * This decrypt function takes a wrapped key `wrapped_key` and using
 * encryption key `key_KEK` outputs a unwrapped key `unwrapped_key`.
 *
 * @param wrapped_key Pointer to the input wrapped key
 * @param key_KEK Input Pointer to the blinded encryption key
 * @param unwrapped_key Pointer to the output unwrapped key struct
 * @return crypto_status_t The result of the aes-kwp decrypt operation
 */
crypto_status_t aes_kwp_decrypt(const crypto_uint8_buf_t wrapped_key,
                                const crypto_blinded_key_t *key_KEK,
                                crypto_blinded_key_t *unwrapped_key);

/**
 * Performs the required hash function on the input data.
 *
 * This function hashes the `input_message` with the selected hash
 * function to return a `digest`. Supported hash modes are
 * kHashModeSha256,kHashModeSha384, kHashModeSha512,
 * kHashModeSha3_224, kHashModeSha3_256, kHashModeSha3_384 and
 * kHashModeSha3_512.
 *
 * @param input_message Input message to be hashed
 * @param hash_mode Required hash mode for the digest
 * @param digest Output digest after hashing the input data
 * @return crypto_status_t The result of the hash operation
 */
crypto_status_t hash(const crypto_uint8_buf_t input_message,
                     hash_mode_t hash_mode, crypto_uint8_buf_t *digest);

/**
 * Performs the required hash xof function on the input data.
 *
 * This function hashes the `input_message` with the selected hash xof
 * function and returns a `digest`. Supported hash modes are
 * kHashModeSha3Shake128, kHashModeSha3Shake256,
 * kHashModeSha3Cshake128 and kHashModeSha3Cshake256.
 *
 * The customization string is passed through `customization_string`
 * parameter. If no customization is desired it can be empty.
 *
 * The function name is used to define functions based on cSHAKE. When
 * no function other than cSHAKE is desired; it can be empty.
 *
 * The `function_name_string` and `customization_string` are ignored
 * when the `hash_mode` is set to kHashModeSha3Shake128 or
 * kHashModeSha3Shake256
 *
 * @param input_message Input message to be hashed
 * @param hash_mode Required hash mode for the digest
 * @param function_name_string NIST Function name string
 * @param customization_string Customization string for kmac
 * @param required_output_len Requested output length from kmac
 * @param digest Output digest after hashing the input data
 * @return crypto_status_t The result of the cshake operation
 */
crypto_status_t hash_xof(const crypto_uint8_buf_t input_message,
                         hash_mode_t hash_mode,
                         crypto_uint8_buf_t function_name_string,
                         crypto_uint8_buf_t customization_string,
                         size_t required_output_len,
                         crypto_uint8_buf_t *digest);

/**
 * Generic hash context.
 *
 * Representation is internal to the hash implementations; initialize with
 * #hash_init.
 */
extern struct hash_context_t;

/**
 * Performs the generic hash init operation.
 *
 * Initializes the generic hash function. Populates the init, update
 * and final function pointers, and digest, block sizes, by calling
 * the respective init function requested by `hash_mode` parameter.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param hash_mode Required hash mode
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t hash_init(hash_context_t *const ctx, hash_mode_t hash_mode);

/**
 * Performs the generic hash update operation.
 *
 * The update operation computes the required hash on `input_meaage`
 * blocks. The intermediate digest is stored in the context `ctx` in
 * the state parameter. Any partial data is stored back in the context
 * partial_data parameter and combined with subsequent bytes.
 *
 * #hash_init should be called before calling this API
 *
 * @param ctx Pointer to the generic hash context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t The result of the update operation
 */
crypto_status_t hash_update(hash_context_t *const ctx,
                            const crypto_uint8_buf_t input_message);

/**
 * Performs the generic hash final operation.
 *
 * The final operation computes the required hash on the remaining
 * partial blocks if any, and then computes the final hash and stores
 * it in the `digest` parameter.
 *
 * #hash_update should be called before calling this API
 *
 * @param ctx Pointer to the generic hash context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t The result of the final operation
 */
crypto_status_t hash_final(hash_context_t *const ctx,
                           crypto_uint8_buf_t *digest);

/**
 * Performs the sha256 init operation.
 *
 * Initializes the sha256 parameters in the `ctx` context, such as the
 * init, update, final functions to use and the digest, block sizes.
 *
 * @param ctx Pointer to the generic hash context struct
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t sha256_init(hash_context_t *const ctx);

/**
 * Performs the sha256 update operation.
 *
 * The update operation computes the sha256 hash on the `input_meaage`
 * blocks. The intermediate digest is stored in the context `ctx` in
 * the state parameter. Any partial data is stored back in the context
 * partial_data parameter and combined with subsequent bytes.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t The result of the update operation
 */
crypto_status_t sha256_update(hash_context_t *const ctx,
                              const crypto_uint8_buf_t input_message);

/**
 * Performs the sha256 final operation.
 *
 * The final operation computes the sha256 hash on the remaining
 * partial blocks if any, and then computes the final hash and stores
 * it in the `digest` parameter.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t The result of the final operation
 */
crypto_status_t sha256_final(hash_context_t *const ctx,
                             crypto_uint8_buf_t *digest);

/**
 * Performs the sha384 init operation.
 *
 * Initializes the sha384 parameters in the `ctx` context, such as the
 * init, update, final functions to use and the digest, block sizes.
 *
 * @param ctx Pointer to the generic hash context struct
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t sha384_init(hash_context_t *const ctx);

/**
 * Performs the sha384 update operation.
 *
 * The update operation computes the sha384 hash on the `input_meaage`
 * blocks. The intermediate digest is stored in the context `ctx` in
 * the state parameter. Any partial data is stored back in the context
 * partial_data parameter and combined with subsequent bytes.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t The result of the update operation
 */
crypto_status_t sha384_update(hash_context_t *const ctx,
                              const crypto_uint8_buf_t input_message);

/**
 * Performs the sha384 final operation.
 *
 * The final operation computes the sha384 hash on the remaining
 * partial blocks if any, and then computes the final hash and stores
 * it in the `digest` parameter.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t The result of the final operation
 */
crypto_status_t sha384_final(hash_context_t *const ctx,
                             crypto_uint8_buf_t *digest);

/**
 * Performs the sha512 init operation.
 *
 * Initializes the sha512 parameters in the `ctx` context, such as the
 * init, update, final functions to use and the digest, block sizes.
 *
 * @param ctx Pointer to the generic hash context struct
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t sha512_init(hash_context_t *const ctx);

/**
 * Performs the sha512 update operation.
 *
 * The update operation computes the sha512 hash on the `input_meaage`
 * blocks. The intermediate digest is stored in the context `ctx` in
 * the state parameter. Any partial data is stored back in the context
 * partial_data parameter and combined with subsequent bytes.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t The result of the update operation
 */
crypto_status_t sha512_update(hash_context_t *const ctx,
                              const crypto_uint8_buf_t input_message);

/**
 * Performs the sha512 final operation.
 *
 * The final operation computes the sha512 hash on the remaining
 * partial blocks if any, and then computes the final hash and stores
 * it in the `digest` parameter.
 *
 * @param ctx Pointer to the generic hash context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t The result of the final operation
 */
crypto_status_t sha512_final(hash_context_t *const ctx,
                             crypto_uint8_buf_t *digest);

/**
 * Performs the mac (hmac/kmac) hash function on the input data.
 *
 * Supported MAc modes are kMacModeHmacSha256, kMacModeKmac128 and
 * kMacModeKmac256
 *
 * HMAC: This function computes the required mac function on the
 * `input_message` using the `key` and returns a `digest`
 *
 * KMAC: This function computes the kmac on the `input_message` using
 * the `key` and returns a `digest` of `required_output_len`. The
 * customization string is passed through `customization_string`
 * parameter. If no customization is desired it can be empty
 *
 * The `customization_string` and `required_output_len` is only used
 * for kmac modes kMacModeKmac128 and kMacModeKmac256, and is ignored
 * when the required mode is set to kMacModeHmacSha256
 *
 * @param key Pointer to the blinded key struct with key shares
 * @param input_message Input message to be hashed
 * @param mac_mode Required MAC mode for the digest (HMAC/KMAC)
 * @param customization_string Customization string for kmac
 * @param required_output_len Requested output length from kmac
 * @param digest Output digest after hashing the input data
 * @return crypto_status_t The result of the kmac128 operation
 */
crypto_status_t mac(const crypto_blinded_key_t *key,
                    const crypto_uint8_buf_t input_message, mac_mode_t mac_mode,
                    crypto_uint8_buf_t customization_string,
                    size_t required_output_len, crypto_uint8_buf_t *digest);

/**
 * Generic hmac context.
 *
 * Representation is internal to the hmac implementations; initialize with
 * #hmac_init.
 */
extern struct hmac_context_t;

/**
 * Performs the generic hmac init operation.
 *
 * Initializes the generic hmac function. Populates the init, update
 * and final function pointers, and digest, block sizes, by calling
 * the respective init function as requested by `hash_mode` parameter.
 *
 * @param ctx Pointer to the generic hmac context struct
 * @param key Pointer to the blinded hmac key struct
 * @param hash_mode Required hash mode
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t hmac_init(hash_context_t *const ctx,
                          const crypto_blinded_key_t *key,
                          hash_mode_t hash_mode);

/**
 * Performs the generic hmac update operation.
 *
 * The update operation computes the required hash on `input_meaage`
 * blocks. The intermediate digest is stored in the context `ctx`, in
 * the state parameter. Any partial data is stored back in the context
 * partial_data parameter and combined with subsequent bytes after.
 *
 * #hmac_init should be called before calling this API
 *
 * @param ctx Pointer to the generic hmac context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t hmac_update(hash_context_t *const ctx,
                            const crypto_uint8_buf_t input_message);

/**
 * Performs the generic hmac final operation.
 *
 * The final operation computes the hash function on the remaining
 * partial blocks if any, and then computes the final hash, and stores
 * the result in the `digest` parameter.
 *
 * #hmac_update should be called before calling this API
 *
 * @param ctx Pointer to the generic hmac context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t The result of the final operation
 */
crypto_status_t hmac_final(hash_context_t *const ctx,
                           crypto_uint8_buf_t *digest);

/**
 * Performs the hmac sha256 init operation.
 *
 * Initializes the hmac sha256 parameters in the `ctx` context, such
 * as the init, update, final functions to use and respective digest,
 * block sizes.
 *
 * @param ctx Pointer to the generic hmac context struct
 * @param key Pointer to the blinded hmac key struct
 * @return crypto_status_t The result of the init operation
 */
crypto_status_t hmac_sha256_init(hash_context_t *const ctx,
                                 const crypto_blinded_key_t *key);

/**
 * Performs the hmac-sha256 update operation.
 *
 * The update operation computes the required hash on `input_meaage`
 * blocks. The intermediate digest is stored in the context `ctx`, in
 * the state parameter. Any partial data is stored back in the context
 * partial_data parameter and combined with subsequent bytes after.
 *
 * @param ctx Pointer to the generic hmac context struct
 * @param input_message Input message to be hashed
 * @return crypto_status_t The result of the update operation
 */
crypto_status_t hmac_sha256_update(hash_context_t *const ctx,
                                   const crypto_uint8_buf_t input_message);

/**
 * Performs the hmac-sha256 final operation.
 *
 * The final operation computes the hash function on the remaining
 * partial blocks if any, and then computes the final hash, and stores
 * the result in the `digest` parameter.
 *
 * @param ctx Pointer to the generic hmac context struct
 * @param digest Output digest after hashing the input blocks
 * @return crypto_status_t The result of the final operation
 */
crypto_status_t hmac_sha256_final(hash_context_t *const ctx,
                                  crypto_uint8_buf_t *digest);

/**
 * Performs the RSA Key generation.
 *
 * Computes RSA private key D and RSA public key E and modulus N. DRBG
 * state is passed as an input parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @param required_key_len Requested key length in bits
 * @param N Pointer to un-blinded key struct with modulus (N)
 * @param E Pointer to un-blinded key struct with public exponent (E)
 * @param D Pointer to blinded key struct with private exponent (D)
 * @return crypto_status_t The result of the rsa key generation
 */
crypto_status_t rsa_keygen(drbg_state_t *drbg_state,
                           crypto_uint8_buf_t additional_input,
                           size_t required_key_len, crypto_unblinded_key_t *N,
                           crypto_unblinded_key_t *E, crypto_blinded_key_t *D);

/**
 * Computes the digital signature on the input message data.
 *
 * @param N Pointer to un-blinded key struct with modulus (N)
 * @param D Pointer to blinded key struct with private exponent (D)
 * @param input_message Input message to be signed
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to generated signature struct
 * @return crypto_status_t The result of the rsa sign generation
 */
crypto_status_t rsa_sign(crypto_unblinded_key_t *N, crypto_blinded_key_t *D,
                         const crypto_uint8_buf_t input_message,
                         rsa_padding_t padding_mode, rsa_hash_t hash_mode,
                         crypto_uint8_buf_t *signature);

/**
 * Verifies the authenticity of the input signature.
 *
 * The generated signature is compared against the input signature and
 * PASS / FAIL is returned
 *
 * @param N Pointer to un-blinded key struct with modulus (N)
 * @param E Pointer to un-blinded key struct with public exponent (E)
 * @param input_message Input message to be signed for verification
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature verification
 * (Pass/Fail)
 * @return crypto_status_t The return status of the rsa verify operation
 */
crypto_status_t rsa_verify(crypto_unblinded_key_t *N, crypto_unblinded_key_t *E,
                           const crypto_uint8_buf_t input_message,
                           rsa_padding_t padding_mode, rsa_hash_t hash_mode,
                           crypto_uint8_buf_t signature,
                           verification_status_t *verification_result);

/**
 * Performs the RSA key generation, asynchronously.
 *
 * Computes RSA private key D and RSA public key E and modulus N. DRBG
 * state is passed as an input parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @param required_key_len Requested key length in bits
 * @param N Pointer to un-blinded key struct with modulus (N)
 * @param E Pointer to un-blinded key struct with public exponent (E)
 * @param D Pointer to blinded key struct with private exponent (D)
 * @return crypto_status_t The result of the rsa key generation
 */
crypto_status_t rsa_keygen_async(drbg_state_t *drbg_state,
                                 crypto_uint8_buf_t additional_input,
                                 size_t required_key_len,
                                 crypto_unblinded_key_t *N,
                                 crypto_unblinded_key_t *E,
                                 crypto_blinded_key_t *D);

/**
 * Computes the digital signature on the input message data, async.
 *
 * @param N Pointer to un-blinded key struct with modulus (N)
 * @param D Pointer to blinded key struct with private exponent (D)
 * @param input_message Input message to be signed
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to generated signature struct
 * @return crypto_status_t The result of the rsa sign generation
 */
crypto_status_t rsa_sign_async(crypto_unblinded_key_t *N,
                               crypto_blinded_key_t *D,
                               const crypto_uint8_buf_t input_message,
                               rsa_padding_t padding_mode, rsa_hash_t hash_mode,
                               crypto_uint8_buf_t *signature);

/**
 * Verifies the authenticity of the input signature, asynchronously.
 *
 * The generated signature is compared against the input signature and
 * PASS / FAIL is returned
 *
 * @param N Pointer to un-blinded key struct with modulus (N)
 * @param E Pointer to un-blinded key struct with public exponent (E)
 * @param input_message Input message to be signed for verification
 * @param padding_mode Padding scheme to be used for the data
 * @param hash_mode Hashing scheme to be used for the signature scheme
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature verification
 * (Pass/Fail)
 * @return crypto_status_t The return status of the rsa verify operation
 */
crypto_status_t rsa_verify_async(crypto_unblinded_key_t *N,
                                 crypto_unblinded_key_t *E,
                                 const crypto_uint8_buf_t input_message,
                                 rsa_padding_t padding_mode,
                                 rsa_hash_t hash_mode,
                                 crypto_uint8_buf_t signature,
                                 verification_status_t *verification_result);

/**
 * Sets the domain parameters of a generic (Weierstrass) ECC curve.
 *
 * @param domain_parameters Pointer to the ecc curve domain parameters
 * @return crypto_status_t The result of the ecc set domain operation
 */
crypto_status_t ecc_set_domain(ecc_domain_t domain_parameters);

/**
 * Sets the domain parameters of a named (Weierstrass) ECC curve.
 *
 * @param named_curve Named curve to set domain parameters for
 * @return crypto_status_t The result of the ecc set domain operation
 */
crypto_status_t ecc_set_domain_named(ecc_named_curve_t named_curve);

/**
 * Performs the ECC Key generation.
 *
 * Computes ECC private exponent (d) and public exponent (Q). DRBG
 * state is passed as an input parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @param required_key_len Requested key length in bits
 * @param private_key Pointer to the blinded private key (D) struct
 * @param public_key Pointer to the unblinded public key (E) struct
 * @return crypto_status_t The result of the ecc key generation
 */
crypto_status_t ecc_keygen(drbg_state_t *drbg_state,
                           crypto_uint8_buf_t additional_input,
                           size_t required_key_len,
                           crypto_blinded_key_t *private_key,
                           ecc_public_key_t *public_key);

/**
 * Performs ECDSA digital signature generation.
 *
 * @param private_key Pointer to the blinded private key (D) struct
 * @param input_message Input message to be signed
 * @param signature Pointer to the ecc sign struct with (r,s) values
 * @return crypto_status_t Result of the ecc signature operation
 */
crypto_status_t ecdsa_sign(crypto_blinded_key_t *private_key,
                           const crypto_uint8_buf_t input_message,
                           ecc_signature_t *signature);

/**
 * Performs ECDSA digital signature verification.
 *
 * @param public_key Pointer to the unblinded public key (E) struct
 * @param input_message Input message to be signed for verification
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature verification
 * (Pass/Fail)
 * @return crypto_status_t Return status of the ecc verification operation
 */
crypto_status_t ecdsa_verify(ecc_public_key_t *public_key,
                             const crypto_uint8_buf_t input_message,
                             ecc_signature_t *signature,
                             verification_status_t *verification_result);

/**
 * Performs Elliptic Curve Diffie Hellman shared secret generation.
 *
 * @param private_key Pointer to the blinded private key (D) struct
 * @param public_key Pointer to the unblinded public key (E) struct
 * @param shared_secret Pointer to generated blinded shared key struct
 * @return crypto_status_t Result of the ecdh operation
 */
crypto_status_t ecc_ecdh(crypto_blinded_key_t *private_key,
                         ecc_public_key_t *public_key,
                         crypto_blinded_key_t *shared_secret);

/**
 * Performs the X25519 Diffie Hellman key exchange function using
 * curve25519.
 *
 * @param private_key Pointer to the blinded private (u-coordinate)
 * @param public_key Pointer to the public scalar from the sender
 * @param shared_secret Pointer to shared secret key (u-coordinate)
 * @return crypto_status_t Result of the ecdh operation
 */
crypto_status_t X25519(crypto_blinded_key_t *private_key,
                       crypto_uint8_buf_t *public_key,
                       crypto_blinded_key_t *shared_secret);

/**
 * Performs the Key generation for the 25519 curve.
 *
 * Computes the private exponent (d) and public exponent (Q) based on
 * the curve 25519. DRBG state is passed as an input parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @param required_key_len Requested key len in bits (256 for Ed25519)
 * @param private_key Pointer to the blinded private key struct
 * @param public_key Pointer to the unblinded public key struct
 * @return crypto_status_t The result of the ecdsa key generation
 */
crypto_status_t ed25519_keygen(drbg_state_t *drbg_state,
                               crypto_uint8_buf_t additional_input,
                               size_t required_key_len,
                               crypto_blinded_key_t *private_key,
                               eddsa_public_key_t *public_key);

/**
 * Performs EdDSA digital signature generation for the Ed25519 curve.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param input_message Input message to be signed
 * @param sign_mode Parameter for Eddsa or Hash EdDSA sign mode
 * @param signature Pointer to the eddsa signature with (r,s) values
 * @return crypto_status_t Result of the eddsa signature operation
 */
crypto_status_t ed25519_sign(crypto_blinded_key_t *private_key,
                             const crypto_uint8_buf_t input_message,
                             eddsa_sign_mode_t sign_mode,
                             ecc_signature_t *signature);

/**
 * Performs EdDSA signature verification for the Ed25519 curve.
 *
 * @param public_key Pointer to the unblinded public key struct
 * @param input_message Input message to be signed for verification
 * @param sign_mode Parameter for Eddsa or Hash EdDSA sign mode
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature verification
 * (Pass/Fail)
 * @return crypto_status_t Return status of the eddsa verification operation
 */
crypto_status_t ed25519_verify(edd_public_key_t *public_key,
                               const crypto_uint8_buf_t input_message,
                               eddsa_sign_mode_t sign_mode,
                               ecc_signature_t *signature,
                               verification_status_t *verification_result);

/**
 * Performs the ECC Key generation, asynchronously.
 *
 * Computes ECC private exponent (d) and public exponent (Q). DRBG
 * state is passed as an input parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @param required_key_len Requested key length in bits
 * @param private_key Pointer to the blinded private key (D) struct
 * @param public_key Pointer to the unblinded public key (E) struct
 * @return crypto_status_t The result of the ecc key generation
 */
crypto_status_t ecc_keygen_async(drbg_state_t *drbg_state,
                                 crypto_uint8_buf_t additional_input,
                                 size_t required_key_len,
                                 crypto_blinded_key_t *private_key,
                                 ecc_public_key_t *public_key);

/**
 * Performs the Key generation for EdDSA, asynchronously.
 *
 * Computes EdDSA private exponent (d) and public exponent (Q). DRBG
 * state is passed as an input parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @param required_key_len Requested key len in bits (256 for Ed25519)
 * @param private_key Pointer to the blinded private key struct
 * @param public_key Pointer to the unblinded public key struct
 * @return crypto_status_t The result of the ecdsa key generation
 */
crypto_status_t eddsa_keygen_async(drbg_state_t *drbg_state,
                                   crypto_uint8_buf_t additional_input,
                                   size_t required_key_len,
                                   crypto_blinded_key_t *private_key,
                                   eddsa_public_key_t *public_key);

/**
 * Performs ECDSA digital signature generation, asynchronously.
 *
 * @param private_key Pointer to the blinded private key (D) struct
 * @param input_message Input message to be signed
 * @param signature Pointer to the ecc sign struct with (r,s) values
 * @return crypto_status_t Result of the ecc signature operation
 */
crypto_status_t ecdsa_sign_async(crypto_blinded_key_t *private_key,
                                 const crypto_uint8_buf_t input_message,
                                 ecc_signature_t *signature);

/**
 * Performs ECDSA digital signature verification, asynchronously.
 *
 * @param public_key Pointer to the unblinded public key (E) struct
 * @param input_message Input message to be signed for verification
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature verification
 * (Pass/Fail)
 * @return crypto_status_t Return status of the ecc verification operation
 */
crypto_status_t ecdsa_verify_async(ecc_public_key_t *public_key,
                                   const crypto_uint8_buf_t input_message,
                                   ecc_signature_t *signature,
                                   verification_status_t *verification_result);

/**
 * Performs the EdDSA digital signature generation for the Ed25519
 * curve, asynchronously.
 *
 * @param private_key Pointer to the blinded private key struct
 * @param input_message Input message to be signed
 * @param sign_mode Parameter for Eddsa or Hash EdDSA sign mode
 * @param signature Pointer to the eddsa signature with (r,s) values
 * @return crypto_status_t Result of the eddsa signature operation
 */
crypto_status_t ed25519_sign_async(crypto_blinded_key_t *private_key,
                                   const crypto_uint8_buf_t input_message,
                                   eddsa_sign_mode_t sign_mode,
                                   ecc_signature_t *signature);

/**
 * Performs the EdDSA signature verification for the Ed25519 curve,
 * asynchronously.
 *
 * @param public_key Pointer to the unblinded public key struct
 * @param input_message Input message to be signed for verification
 * @param sign_mode Parameter for Eddsa or Hash EdDSA sign mode
 * @param signature Pointer to the signature to be verified
 * @param verification_result Returns the result of signature verification
 * (Pass/Fail)
 * @return crypto_status_t Return status of the eddsa verification operation
 */
crypto_status_t ed25519_verify_async(
    edd_public_key_t *public_key, const crypto_uint8_buf_t input_message,
    eddsa_sign_mode_t sign_mode, ecc_signature_t *signature,
    verification_status_t *verification_result);

/**
 * DRBG state.
 */
extern struct drbg_state_t;

/**
 * Initializes the DRBG.
 *
 * Initializes DRBG and the context parameter for DRBG. Gets the
 * entropy input automatically from the entropy source.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param nonce Pointer to the nonce bit-string
 * @param personalization_string Pointer to personalization bitstring
 * @return crypto_status_t Result of the drbg instantiate operation
 */
crypto_status_t drbg_instantiate(drbg_state_t *drbg_state,
                                 crypto_uint8_buf_t nonce,
                                 crypto_uint8_buf_t personalization_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with fresh entropy automatically fetched from the
 * entropy source and updates the working state parameters.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional input for drbg
 * @return crypto_status_t Result of the drbg reseed operation
 */
crypto_status_t drbg_reseed(drbg_state_t *drbg_state,
                            crypto_uint8_buf_t additional_input);

/**
 * Initializes the DRBG.
 *
 * Initializes DRBG and the context parameter for DRBG. Gets the
 * entropy input from the user through `entropy` parameter.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param entropy Pointer to the user defined entropy value
 * @param nonce Pointer to the nonce bit-string
 * @param personalization_string Pointer to personalization bitstring
 * @return crypto_status_t Result of the drbg instantiate operation
 */
crypto_status_t drbg_manual_instantiate(
    drbg_state_t *drbg_state, crypto_uint8_buf_t entropy,
    crypto_uint8_buf_t nonce, crypto_uint8_buf_t personalization_string);

/**
 * Reseeds the DRBG with fresh entropy.
 *
 * Reseeds the DRBG with entropy input from the user through `entropy`
 * parameter and updates the working state parameters.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param entropy Pointer to the user defined entropy value
 * @param additional_input Pointer to the additional input for drbg
 * @return crypto_status_t Result of the drbg reseed operation
 */
crypto_status_t drbg_manual_reseed(drbg_state_t *drbg_state,
                                   crypto_uint8_buf_t entropy,
                                   crypto_uint8_buf_t additional_input);

/**
 * DRBG function for generating random bits.
 *
 * Used to generate pseudo random bits after drbg instantiation or
 * drbg reseeding.
 *
 * @param drbg_state Pointer to the drbg working state
 * @param additional_input Pointer to the additional data
 * @param drbg_output Pointer to the generated pseudo random bits
 * @return crypto_status_t Result of the drbg generate operation
 */
crypto_status_t drbg_generate(drbg_state_t *drbg_state,
                              crypto_uint8_buf_t additional_input,
                              crypto_uint8_buf_t *drbg_output);

/**
 * Uninstantiates DRBG and clears the context.
 *
 * @param drbg_state Pointer to the drbg working state
 * @return crypto_status_t Result of the drbg uninstantiate operation
 */
crypto_status_t drbg_uninstantiate(drbg_state_t *drbg_state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_API_H_
