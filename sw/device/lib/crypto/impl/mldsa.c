// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/mldsa.h"

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'l', 'd')

otcrypto_status_t otcrypto_mldsa87_keygen(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_t message, const otcrypto_const_byte_t context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_word32_buf_t signature) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t message,
    const otcrypto_const_byte_t context, otcrypto_mldsa87_hash_mode_t hash_mode,
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keycheck(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keygen_async_start(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keygen_async_finalize(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_t message, const otcrypto_const_byte_t context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_word32_buf_t signature) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_sign_async_finalize(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_t message, const otcrypto_const_byte_t context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_word32_buf_t signature) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t message,
    const otcrypto_const_byte_t context, otcrypto_mldsa87_hash_mode_t hash_mode,
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_verify_async_finalize(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t message,
    const otcrypto_const_byte_t context, otcrypto_mldsa87_hash_mode_t hash_mode,
    otcrypto_const_word32_buf_t signature,
    hardened_bool_t *verification_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keycheck_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keycheck_async_finalize(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
