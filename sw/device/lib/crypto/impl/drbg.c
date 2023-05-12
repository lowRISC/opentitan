// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/drbg.h"

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'b', 'g')

crypto_status_t otcrypto_drbg_instantiate(crypto_uint8_buf_t nonce,
                                          crypto_uint8_buf_t perso_string) {
  // TODO: Connect entropy driver to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_drbg_reseed(crypto_uint8_buf_t additional_input) {
  // TODO: Connect entropy driver to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_drbg_manual_instantiate(
    crypto_uint8_buf_t entropy, crypto_uint8_buf_t nonce,
    crypto_uint8_buf_t perso_string) {
  // TODO: Connect entropy driver to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_drbg_manual_reseed(
    crypto_uint8_buf_t entropy, crypto_uint8_buf_t additional_input) {
  // TODO: Connect entropy driver to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_drbg_generate(crypto_uint8_buf_t additional_input,
                                       size_t output_len,
                                       crypto_uint8_buf_t *drbg_output) {
  // TODO: Connect entropy driver to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
