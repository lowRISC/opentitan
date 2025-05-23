// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_encryption.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_modexp.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_padding.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'e', 'n')

status_t rsa_encrypt_2048_start(const rsa_2048_public_key_t *public_key,
                                const otcrypto_hash_mode_t hash_mode,
                                const uint8_t *message, size_t message_bytelen,
                                const uint8_t *label, size_t label_bytelen) {
  // Encode the message.
  rsa_2048_int_t encoded_message;
  hardened_memshred(encoded_message.data, ARRAYSIZE(encoded_message.data));
  HARDENED_TRY(rsa_padding_oaep_encode(
      hash_mode, message, message_bytelen, label, label_bytelen,
      ARRAYSIZE(encoded_message.data), encoded_message.data));

  // Start computing (encoded_message ^ e) mod n with a variable-time
  // exponentiation.
  return rsa_modexp_vartime_2048_start(&encoded_message, public_key->e,
                                       &public_key->n);
}

status_t rsa_encrypt_2048_finalize(rsa_2048_int_t *ciphertext) {
  return rsa_modexp_2048_finalize(ciphertext);
}

status_t rsa_decrypt_2048_start(const rsa_2048_private_key_t *private_key,
                                const rsa_2048_int_t *ciphertext) {
  // Start computing (ciphertext ^ d) mod n.
  return rsa_modexp_consttime_2048_start(ciphertext, &private_key->d,
                                         &private_key->n);
}

status_t rsa_decrypt_finalize(const otcrypto_hash_mode_t hash_mode,
                              const uint8_t *label, size_t label_bytelen,
                              size_t plaintext_max_bytelen, uint8_t *plaintext,
                              size_t *plaintext_len) {
  // Wait for OTBN to complete and get the size for the last RSA operation.
  size_t num_words;
  HARDENED_TRY(rsa_modexp_wait(&num_words));

  // Check that enough space has been allocated for the plaintext.
  size_t max_plaintext_bytelen = 0;
  HARDENED_TRY(rsa_padding_oaep_max_message_bytelen(hash_mode, num_words,
                                                    &max_plaintext_bytelen));
  if (plaintext_max_bytelen < max_plaintext_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GE(plaintext_max_bytelen, max_plaintext_bytelen);

  // Randomize the plaintext destination buffer as best we can, considering its
  // alignment.
  ptrdiff_t misalignment = misalignment32_of((uintptr_t)plaintext);
  size_t aligned_offset =
      (sizeof(uint32_t) - (size_t)misalignment) % sizeof(uint32_t);
  size_t num_aligned_full_words =
      (plaintext_max_bytelen - aligned_offset) / sizeof(uint32_t);
  hardened_memshred((uint32_t *)((uintptr_t)plaintext + aligned_offset),
                    num_aligned_full_words);

  // Call the appropriate `finalize()` operation to get the recovered encoded
  // message.
  switch (num_words) {
    case kRsa2048NumWords: {
      rsa_2048_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_2048_finalize(&recovered_message));
      return rsa_padding_oaep_decode(
          hash_mode, label, label_bytelen, recovered_message.data,
          ARRAYSIZE(recovered_message.data), plaintext, plaintext_len);
    }
    case kRsa3072NumWords: {
      rsa_3072_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_3072_finalize(&recovered_message));
      return rsa_padding_oaep_decode(
          hash_mode, label, label_bytelen, recovered_message.data,
          ARRAYSIZE(recovered_message.data), plaintext, plaintext_len);
    }
    case kRsa4096NumWords: {
      rsa_4096_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_4096_finalize(&recovered_message));
      return rsa_padding_oaep_decode(
          hash_mode, label, label_bytelen, recovered_message.data,
          ARRAYSIZE(recovered_message.data), plaintext, plaintext_len);
    }
    default:
      // Unexpected number of words; should never get here.
      return OTCRYPTO_FATAL_ERR;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

status_t rsa_encrypt_3072_start(const rsa_3072_public_key_t *public_key,
                                const otcrypto_hash_mode_t hash_mode,
                                const uint8_t *message, size_t message_bytelen,
                                const uint8_t *label, size_t label_bytelen) {
  // Encode the message.
  rsa_3072_int_t encoded_message;
  hardened_memshred(encoded_message.data, ARRAYSIZE(encoded_message.data));
  HARDENED_TRY(rsa_padding_oaep_encode(
      hash_mode, message, message_bytelen, label, label_bytelen,
      ARRAYSIZE(encoded_message.data), encoded_message.data));

  // Start computing (encoded_message ^ e) mod n with a variable-time
  // exponentiation.
  return rsa_modexp_vartime_3072_start(&encoded_message, public_key->e,
                                       &public_key->n);
}

status_t rsa_encrypt_3072_finalize(rsa_3072_int_t *ciphertext) {
  return rsa_modexp_3072_finalize(ciphertext);
}

status_t rsa_decrypt_3072_start(const rsa_3072_private_key_t *private_key,
                                const rsa_3072_int_t *ciphertext) {
  // Start computing (ciphertext ^ d) mod n.
  return rsa_modexp_consttime_3072_start(ciphertext, &private_key->d,
                                         &private_key->n);
}

status_t rsa_encrypt_4096_start(const rsa_4096_public_key_t *public_key,
                                const otcrypto_hash_mode_t hash_mode,
                                const uint8_t *message, size_t message_bytelen,
                                const uint8_t *label, size_t label_bytelen) {
  // Encode the message.
  rsa_4096_int_t encoded_message;
  hardened_memshred(encoded_message.data, ARRAYSIZE(encoded_message.data));
  HARDENED_TRY(rsa_padding_oaep_encode(
      hash_mode, message, message_bytelen, label, label_bytelen,
      ARRAYSIZE(encoded_message.data), encoded_message.data));

  // Start computing (encoded_message ^ e) mod n with a variable-time
  // exponentiation.
  return rsa_modexp_vartime_4096_start(&encoded_message, public_key->e,
                                       &public_key->n);
}

status_t rsa_encrypt_4096_finalize(rsa_4096_int_t *ciphertext) {
  return rsa_modexp_4096_finalize(ciphertext);
}

status_t rsa_decrypt_4096_start(const rsa_4096_private_key_t *private_key,
                                const rsa_4096_int_t *ciphertext) {
  // Start computing (ciphertext ^ d) mod n.
  return rsa_modexp_consttime_4096_start(ciphertext, &private_key->d,
                                         &private_key->n);
}
