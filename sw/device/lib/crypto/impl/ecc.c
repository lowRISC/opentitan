// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc.h"

#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', 'c', 'c')

crypto_status_t otcrypto_ecdsa_keygen(ecc_curve_t *elliptic_curve,
                                      crypto_blinded_key_t *private_key,
                                      ecc_public_key_t *public_key) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_sign(const crypto_blinded_key_t *private_key,
                                    crypto_const_uint8_buf_t input_message,
                                    ecc_curve_t *elliptic_curve,
                                    ecc_signature_t *signature) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_verify(
    const ecc_public_key_t *public_key, crypto_const_uint8_buf_t input_message,
    ecc_signature_t *signature, ecc_curve_t *elliptic_curve,
    verification_status_t *verification_result) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdh_keygen(ecc_curve_t *elliptic_curve,
                                     crypto_blinded_key_t *private_key,
                                     ecc_public_key_t *public_key) {
  // TODO: Connect ECDH operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdh(const crypto_blinded_key_t *private_key,
                              const ecc_public_key_t *public_key,
                              ecc_curve_t *elliptic_curve,
                              crypto_blinded_key_t *shared_secret) {
  // TODO: Connect ECDH operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_keygen(crypto_blinded_key_t *private_key,
                                        crypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_sign(const crypto_blinded_key_t *private_key,
                                      crypto_const_uint8_buf_t input_message,
                                      eddsa_sign_mode_t sign_mode,
                                      ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_verify(
    const crypto_unblinded_key_t *public_key,
    crypto_const_uint8_buf_t input_message, eddsa_sign_mode_t sign_mode,
    ecc_signature_t *signature, verification_status_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_x25519_keygen(crypto_blinded_key_t *private_key,
                                       crypto_unblinded_key_t *public_key) {
  // TODO: Connect X25519 operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_x25519(const crypto_blinded_key_t *private_key,
                                const crypto_unblinded_key_t *public_key,
                                crypto_blinded_key_t *shared_secret) {
  // TODO: Connect X25519 operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_keygen_async_start(ecc_curve_t *elliptic_curve) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_keygen_async_finalize(
    crypto_blinded_key_t *private_key, ecc_public_key_t *public_key) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_uint8_buf_t input_message, ecc_curve_t *elliptic_curve) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_sign_async_finalize(ecc_signature_t *signature) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_verify_async_start(
    const ecc_public_key_t *public_key, crypto_const_uint8_buf_t input_message,
    ecc_signature_t *signature, ecc_curve_t *elliptic_curve) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdsa_verify_async_finalize(
    verification_status_t *verification_result) {
  // TODO: Connect ECDSA operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdh_keygen_async_start(ecc_curve_t *elliptic_curve) {
  // TODO: Connect ECDH operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdh_keygen_async_finalize(
    crypto_blinded_key_t *private_key, ecc_public_key_t *public_key) {
  // TODO: Connect ECDH operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdh_async_start(
    const crypto_blinded_key_t *private_key, const ecc_public_key_t *public_key,
    ecc_curve_t *elliptic_curve) {
  // TODO: Connect ECDH operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ecdh_async_finalize(
    crypto_blinded_key_t *shared_secret) {
  // TODO: Connect ECDH operations to API.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_keygen_async_start() {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_sign_async_start(
    const crypto_blinded_key_t *private_key,
    crypto_const_uint8_buf_t input_message, eddsa_sign_mode_t sign_mode,
    ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_sign_async_finalize(
    ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_verify_async_start(
    const crypto_unblinded_key_t *public_key,
    crypto_const_uint8_buf_t input_message, eddsa_sign_mode_t sign_mode,
    ecc_signature_t *signature) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_ed25519_verify_async_finalize(
    verification_status_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_x25519_keygen_async_start() {
  // TODO: X25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_x25519_keygen_async_finalize(
    crypto_blinded_key_t *private_key, crypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_x25519_async_start(
    const crypto_blinded_key_t *private_key,
    const crypto_unblinded_key_t *public_key) {
  // TODO: X25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}

crypto_status_t otcrypto_x25519_async_finalize(
    crypto_blinded_key_t *shared_secret) {
  // TODO: X25519 is not yet implemented.
  return kCryptoStatusNotImplemented;
}
