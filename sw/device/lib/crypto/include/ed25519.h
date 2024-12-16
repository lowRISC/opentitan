/**
 * Enum to define EdDSA mode for signature.
 *
 * Values are hardened.
 */
typedef enum otcrypto_eddsa_sign_mode {
  // Signature mode EdDSA.
  kOtcryptoEddsaSignModeEddsa = 0xae1,
  // Signature mode Hashed EdDSA.
  kOtcryptoEddsaSignModeHashEddsa = 0x9a6,
} otcrypto_eddsa_sign_mode_t;

/**
 * Generates a new Ed25519 key pair.
 *
 * Computes the private exponent (d) and public key (Q) based on
 * Curve25519.
 *
 * No `domain_parameter` is needed and is automatically set for Ed25519.
 *
 * The caller should allocate and partially populate the blinded key struct,
 * including populating the key configuration and allocating space for the
 * keyblob. The caller should indicate the length of the allocated keyblob;
 * this function will return an error if the keyblob length does not match
 * expectations. If the key is hardware-backed, the caller should pass a fully
 * populated private key handle as returned by `otcrypto_hw_backed_key`. For
 * non-hardware-backed keys, the keyblob should be twice the length of the key.
 * The value in the `checksum` field of the blinded key struct will be
 * populated by the key generation function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of the Ed25519 key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen(otcrypto_blinded_key_t *private_key,
                                          otcrypto_unblinded_key_t *public_key);

/**
 * Generates an Ed25519 digital signature.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param input_message Input message to be signed.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param[out] signature Pointer to the EdDSA signature with (r,s) values.
 * @return Result of the EdDSA signature generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature);

/**
 * Verifies an Ed25519 signature.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Input message to be signed for verification.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param signature Pointer to the signature to be verified.
 * @param[out] verification_result Result of signature verification
 * (Pass/Fail).
 * @return Result of the EdDSA verification operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result);

/**
 * Starts the asynchronous key generation for Ed25519.
 *
 * Initializes OTBN and begins generating an Ed25519 key pair. The caller
 * should set the `config` field of `private_key` with their desired key
 * configuration options. If the key is hardware-backed, the caller should pass
 * a fully populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`.
 *
 * No `domain_parameter` is needed and is automatically set for X25519.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous ed25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for Ed25519.
 *
 * Returns `kOtcryptoStatusValueOk` and copies private key (d) and public key
 * (Q), if the OTBN status is done, or `kOtcryptoStatusValueAsyncIncomplete`
 * if the OTBN is busy or `kOtcryptoStatusValueInternalError` if there is an
 * error.
 *
 * The caller must ensure that `config` matches the key configuration initially
 * passed to the `_start` complement of this function.
 *
 * @param[out] private_key Pointer to the blinded private key struct.
 * @param[out] public_key Pointer to the unblinded public key struct.
 * @return Result of asynchronous ed25519 keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous Ed25519 digital signature generation.
 *
 * Initializes OTBN and starts the OTBN routine to compute the digital
 * signature on the input message. The `domain_parameter` field for
 * Ed25519 is automatically set.
 *
 * @param private_key Pointer to the blinded private key struct.
 * @param input_message Input message to be signed.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param[out] signature Pointer to the EdDSA signature to get (r) value.
 * @return Result of async Ed25519 start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature);

/**
 * Finalizes the asynchronous Ed25519 digital signature generation.
 *
 * Returns `kOtcryptoStatusValueOk` and copies the signature if the OTBN
 * status is done, or `kOtcryptoStatusValueAsyncIncomplete` if the OTBN is
 * busy or `kOtcryptoStatusValueInternalError` if there is an error.
 *
 * @param[out] signature Pointer to the EdDSA signature to get (s) value.
 * @return Result of async Ed25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t signature);

/**
 * Starts the asynchronous Ed25519 digital signature verification.
 *
 * Initializes OTBN and starts the OTBN routine to verify the
 * signature. The `domain_parameter` for Ed25519 is set automatically.
 *
 * @param public_key Pointer to the unblinded public key struct.
 * @param input_message Input message to be signed for verification.
 * @param sign_mode Parameter for EdDSA or Hash EdDSA sign mode.
 * @param signature Pointer to the signature to be verified.
 * @return Result of async Ed25519 verification start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    otcrypto_const_word32_buf_t signature);

/**
 * Finalizes the asynchronous Ed25519 digital signature verification.
 *
 * Returns `kOtcryptoStatusValueOk` and populates the `verification result`
 * with a PASS or FAIL, if the OTBN status is done,
 * `kOtcryptoStatusValueAsyncIncomplete` if the OTBN is busy or
 * `kOtcryptoStatusValueInternalError` if there is an error.
 *
 * @param[out] verification_result Result of signature verification
 * (Pass/Fail).
 * @return Result of async Ed25519 verification finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result);
