// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/key_transport.h"

#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/drbg.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 't', 'r')

crypto_status_t otcrypto_symmetric_keygen(crypto_const_byte_buf_t perso_string,
                                          crypto_blinded_key_t *key) {
  if (key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure that the key material is masked with XOR; this will fail on
  // hardware-backed or non-symmetric keys.
  HARDENED_TRY(keyblob_ensure_xor_masked(key->config));

  // Get pointers to the shares within the keyblob. Fails if the key length
  // doesn't match the mode.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key, &share0, &share1));

  // Construct buffers to direct the DRBG output into the keyblob.
  crypto_word32_buf_t share0_buf = {
      .data = share0,
      .len = keyblob_share_num_words(key->config),
  };
  crypto_word32_buf_t share1_buf = {
      .data = share1,
      .len = keyblob_share_num_words(key->config),
  };

  // Construct an empty buffer for the "additional input" to the DRBG generate
  // function.
  crypto_const_byte_buf_t empty = {.data = NULL, .len = 0};

  // Generate each share of the key independently.
  HARDENED_TRY(otcrypto_drbg_instantiate(perso_string));
  HARDENED_TRY(otcrypto_drbg_generate(empty, &share0_buf));
  HARDENED_TRY(otcrypto_drbg_generate(empty, &share1_buf));

  // Populate the checksum and return.
  key->checksum = integrity_blinded_checksum(key);
  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hw_backed_key(uint32_t version, const uint32_t salt[7],
                                       crypto_blinded_key_t *key) {
  if (key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (key->keyblob_length != 8 * sizeof(uint32_t) ||
      key->config.hw_backed != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get the key type from the top 16 bits of the full mode and ensure that it
  // is not RSA. All other key types are acceptable for hardware-backed keys.
  key_type_t key_type = (key_type_t)(key->config.key_mode >> 16);
  if (key_type == kKeyTypeRsa) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Copy the version and salt into the keyblob.
  key->keyblob[0] = version;
  memcpy(&key->keyblob[1], salt, 7 * sizeof(uint32_t));

  // Set the checksum.
  key->checksum = integrity_blinded_checksum(key);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_build_unblinded_key(
    crypto_const_byte_buf_t plain_key, key_mode_t key_mode,
    crypto_unblinded_key_t unblinded_key) {
  // TODO: implement key transport functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_build_blinded_key(crypto_const_byte_buf_t plain_key,
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
