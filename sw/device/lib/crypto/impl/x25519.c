// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/x25519.h"

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('x', '2', '5')

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
