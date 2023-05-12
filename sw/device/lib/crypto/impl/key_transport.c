// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/key_transport.h"

#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 't', 'r')

crypto_status_t otcrypto_build_unblinded_key(
    crypto_const_uint8_buf_t plain_key, key_mode_t key_mode,
    crypto_unblinded_key_t unblinded_key) {
  // TODO: implement key transport functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_build_blinded_key(crypto_const_uint8_buf_t plain_key,
                                           crypto_blinded_key_t blinded_key) {
  // TODO: implement key transport functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_blinded_to_unblinded_key(
    const crypto_blinded_key_t blinded_key,
    crypto_unblinded_key_t unblinded_key) {
  // TODO: implement key transport functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_unblinded_to_blinded_key(
    const crypto_unblinded_key_t unblinded_key,
    crypto_blinded_key_t blinded_key) {
  // TODO: implement key transport functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
