// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/ecc.h"

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('e', 'c', 'c')

otcrypto_status_t otcrypto_ed25519_keygen(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_sign(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_verify(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

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

/**
 * Calls keymgr to sideload key material into OTBN.
 *
 * This routine should only ever be called on hardware-backed keys.
 *
 * @param private_key Sideloaded key handle.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t sideload_key_seed(const otcrypto_blinded_key_t *private_key) {
  keymgr_diversification_t diversification;
  HARDENED_TRY(
      keyblob_to_keymgr_diversification(private_key, &diversification));
  return keymgr_generate_key_otbn(diversification);
}

otcrypto_status_t otcrypto_ed25519_keygen_async_start(
    const otcrypto_blinded_key_t *private_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_keygen_async_finalize(
    otcrypto_blinded_key_t *private_key, otcrypto_unblinded_key_t *public_key) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode, otcrypto_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_sign_async_finalize(
    otcrypto_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    otcrypto_const_byte_buf_t input_message,
    otcrypto_eddsa_sign_mode_t sign_mode,
    otcrypto_const_word32_buf_t signature) {
  // TODO: Ed25519 is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_ed25519_verify_async_finalize(
    hardened_bool_t *verification_result) {
  // TODO: Ed25519 is not yet implemented.
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
