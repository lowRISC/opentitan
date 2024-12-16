

otcrypto_status_t otcrypto_x25519_keygen(otcrypto_blinded_key_t *private_key,
                                         otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect X25519 operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519(const otcrypto_blinded_key_t *private_key,
                                  const otcrypto_unblinded_key_t *public_key,
                                  otcrypto_blinded_key_t *shared_secret) {
  // TODO: Connect X25519 operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_x25519_async_finalize(
    otcrypto_blinded_key_t *shared_secret) {
  // TODO: X25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
