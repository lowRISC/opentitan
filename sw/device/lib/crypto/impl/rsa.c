// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/rsa.h"

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 's', 'a')

crypto_status_t otcrypto_rsa_keygen(rsa_key_size_t required_key_len,
                                    rsa_public_key_t *rsa_public_key,
                                    rsa_private_key_t *rsa_private_key) {
  // TODO: Implement RSA key generation.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_sign(const rsa_private_key_t *rsa_private_key,
                                  crypto_const_uint8_buf_t input_message,
                                  rsa_padding_t padding_mode,
                                  rsa_hash_t hash_mode,
                                  crypto_uint8_buf_t *signature) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_verify(const rsa_public_key_t *rsa_public_key,
                                    crypto_const_uint8_buf_t input_message,
                                    rsa_padding_t padding_mode,
                                    rsa_hash_t hash_mode,
                                    crypto_const_uint8_buf_t signature,
                                    hardened_bool_t *verification_result) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_keygen_async_start(
    rsa_key_size_t required_key_len) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_keygen_async_finalize(
    rsa_public_key_t *rsa_public_key, rsa_private_key_t *rsa_private_key) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_sign_async_start(
    const rsa_private_key_t *rsa_private_key,
    crypto_const_uint8_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_sign_async_finalize(
    crypto_uint8_buf_t *signature) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_verify_async_start(
    const rsa_public_key_t *rsa_public_key,
    crypto_const_uint8_buf_t signature) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_rsa_verify_async_finalize(
    crypto_const_uint8_buf_t input_message, rsa_padding_t padding_mode,
    rsa_hash_t hash_mode, hardened_bool_t *verification_result) {
  // TODO: Connect RSA implementations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
