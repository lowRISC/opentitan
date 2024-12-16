
/**
 * Generates a new key pair for X25519 key exchange.
 *
 * Computes the private scalar (d) and public key (Q) based on
 * Curve25519.
 *
 * No `domain_parameter` is needed and is automatically set for X25519.
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
 * @return Result of the X25519 key generation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen(otcrypto_blinded_key_t *private_key,
                                         otcrypto_unblinded_key_t *public_key);

/**
 * Performs the X25519 Diffie Hellman shared secret generation.
 *
 * @param private_key Pointer to blinded private key (u-coordinate).
 * @param public_key Pointer to the public scalar from the sender.
 * @param[out] shared_secret Pointer to shared secret key (u-coordinate).
 * @return Result of the X25519 operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519(const otcrypto_blinded_key_t *private_key,
                                  const otcrypto_unblinded_key_t *public_key,
                                  otcrypto_blinded_key_t *shared_secret);

/**
 * Starts the asynchronous key generation for X25519.
 *
 * Initializes OTBN and begins generating an X25519 key pair. The caller
 * should set the `config` field of `private_key` with their desired key
 * configuration options. If the key is hardware-backed, the caller should pass
 * a fully populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`.
 *
 * No `domain_parameter` is needed and is automatically set for X25519.
 *
 * @param private_key Destination structure for private key, or key handle.
 * @return Result of asynchronous X25519 keygen start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key);

/**
 * Finalizes the asynchronous key generation for X25519.
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
 * @return Result of asynchronous X25519 keygen finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key);

/**
 * Starts the asynchronous X25519 Diffie Hellman shared secret
 * generation.
 *
 * Initializes OTBN and starts the OTBN routine to perform Diffie
 * Hellman shared secret generation based on Curve25519. The
 * domain parameter is automatically set for X25519 API.
 *
 * @param private_key Pointer to the blinded private key (u-coordinate).
 * @param public_key Pointer to the public scalar from the sender.
 * @return Result of the async X25519 start operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key);

/**
 * Finalizes the asynchronous X25519 Diffie Hellman shared secret
 * generation.
 *
 * Returns `kOtcryptoStatusValueOk` and copies `shared_secret` if the OTBN
 * status is done, or `kOtcryptoStatusValueAsyncIncomplete` if the OTBN
 * is busy or `kOtcryptoStatusValueInternalError` if there is an error.
 *
 * @param[out] shared_secret Pointer to shared secret key (u-coordinate).
 * @return Result of async X25519 finalize operation.
 */
OT_WARN_UNUSED_RESULT
otcrypto_status_t otcrypto_x25519_async_finalize(
    otcrypto_blinded_key_t *shared_secret);
