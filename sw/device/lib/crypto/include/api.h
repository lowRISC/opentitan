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
 * @return Result of the hash operation
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
 * @return Result of the xof operation
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
 * @return Result of the hash init operation
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
 * @return Result of the hash update operation
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
 * @return Result of the hash final operation
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
 * @return The result of the KMAC128 operation
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
 * @return Result of the HMAC init operation
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
 * @return Result of the HMAC update operation
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
 * @return Result of the HMAC final operation
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
 * @return Result of the RSA key generation
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
 * @return The result of the RSA sign generation
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
 * @return The status of the RSA verify operation
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
 * @return Result of the ECDSA key generation
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
 * @return Result of the ECDSA signature generation
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
 * @return Result of the deterministic ECDSA signature
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
 * @return Result of the ECDSA verification operation
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
 * @return Result of the ECDH key generation
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
 * @return Result of ECDH shared secret generation
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
 * @return Result of the Ed25519 key generation
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
 * @return Result of the EdDSA signature generation
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
 * @return Result of the EdDSA verification operation
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
 * @return Result of the X25519 key generation
 */
crypto_status_t otcrypto_x25519_keygen(crypto_blinded_key_t *private_key,
                                       crypto_unblinded_key_t *public_key);

/**
 * Performs the X25519 Diffie Hellman shared secret generation.
 *
 * @param private_key Pointer to blinded private key (u-coordinate)
 * @param public_key Pointer to the public scalar from the sender
 * @param shared_secret Pointer to shared secret key (u-coordinate)
 * @return Result of the X25519 operation
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
 * @return Result of async RSA keygen start operation
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
 * @return Result of asynchronous RSA keygen finalize
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
 * @return Result of async RSA sign start operation
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
 * @return Result of async RSA sign finalize operation
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
 * @return Result of async RSA verify start operation
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
 * @return Result of async RSA verify finalize
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
 * @return Result of asynchronous ECDSA keygen start
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
 * @return Result of asynchronous ECDSA keygen
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
 * @return Result of async ECDSA start operation
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
 * @return Result of async ECDSA finalize operation
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
 * @return Result of async ECDSA start operation
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
 * @return Result of async deterministic ECDSA finalize
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
 * @return Result of async ECDSA verify start function
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
 * @return Result of async ECDSA verify finalize
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
 * @return Result of asynchronous ECDH keygen start
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
 * @return Result of asynchronous ECDH keygen
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
 * @return Result of async ECDH start operation
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
 * @return Result of async ECDH finalize operation
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
 * @return Result of asynchronous ed25519 keygen start
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
 * @return Result of asynchronous ed25519 keygen
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
 * @return Result of async Ed25519 start operation
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
 * @return Result of async Ed25519 finalize operation
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
 * @return Result of async Ed25519 verification start
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
 * @return Result of async Ed25519 verification
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
 * @return Result of asynchronous X25519 keygen start
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
 * @return Result of asynchronous X25519 keygen
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
 * @return Result of the async X25519 start operation
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
 * @return Result of async X25519 finalize operation
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
 * @return Result of the DRBG instantiate operation
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
 * @return Result of the DRBG reseed operation
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
 * @return Result of the DRBG manual instantiation
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
 * @return Result of the manual DRBG reseed operation
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
 * @return Result of the DRBG generate operation
 */
crypto_status_t otcrypto_drbg_generate(drbg_state_t *drbg_state,
                                       crypto_uint8_buf_t additional_input,
                                       size_t output_len,
                                       crypto_uint8_buf_t *drbg_output);

/**
 * Uninstantiates DRBG and clears the context.
 *
 * @param drbg_state Pointer to the DRBG working state
 * @return Result of the DRBG uninstantiate operation
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
 * @return Result of the key derivation operation
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
 * @return Result of the build unblinded key operation
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
 * @return Result of the build blinded key operation
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
 * @return Result of the blinded key export operation
 */
crypto_status_t otcrypto_blinded_to_unblinded_key(
    const crypto_blinded_key_t blinded_key,
    crypto_unblinded_key_t unblinded_key);

/**
 * Build a blinded key struct from an unblinded key struct.
 *
 * @param unblinded_key Blinded key struct to be unmasked
 * @param blinded_key Generated (unmasked) unblinded key struct
 * @return Result of unblinded key export operation
 */
crypto_status_t otcrypto_unblinded_to_blinded_key(
    const crypto_unblinded_key unblinded_key, crypto_blinded_key_t blinded_key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_API_H_
