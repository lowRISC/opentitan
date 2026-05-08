// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_encryption.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_padding.h"
#include "sw/device/lib/crypto/impl/rsa/run_rsa.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'e', 'n')

status_t rsa_encrypt_start(rsa_size_t size, const uint32_t *n,
                           const otcrypto_hash_mode_t hash_mode,
                           const uint8_t *message, size_t message_bytelen,
                           const uint8_t *label, size_t label_bytelen) {
  size_t num_words = 0;
  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      num_words = kRsa2048NumWords;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Allocate maximum possible size to avoid VLAs. We allocate enough for
  // 4096, but will only utilize `num_words`.
  uint32_t encoded_message[kRsa4096NumWords];

  // Encode the message.
  HARDENED_TRY(hardened_memshred(encoded_message, ARRAYSIZE(encoded_message)));
  HARDENED_TRY(rsa_padding_oaep_encode(hash_mode, message, message_bytelen,
                                       label, label_bytelen, num_words,
                                       encoded_message));

  // Start computing (encoded_message ^ e) mod n with a variable-time
  // exponentiation.
  return rsa_modexp_vartime_start(size, encoded_message, n);
}

status_t rsa_encrypt_finalize(rsa_size_t size, uint32_t *ciphertext) {
  return rsa_modexp_finalize_size(size, ciphertext);
}

status_t rsa_decrypt_start(rsa_size_t size, const uint32_t *d0,
                           const uint32_t *d1, const uint32_t *n,
                           const uint32_t *ciphertext) {
  // Start computing (ciphertext ^ d) mod n.
  return rsa_modexp_consttime_start(size, ciphertext, d0, d1, n);
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
  if (plaintext_max_bytelen < aligned_offset) {
    return OTCRYPTO_BAD_ARGS;
  }
  size_t num_aligned_full_words =
      (plaintext_max_bytelen - aligned_offset) / sizeof(uint32_t);
  HARDENED_TRY(
      hardened_memshred((uint32_t *)((uintptr_t)plaintext + aligned_offset),
                        num_aligned_full_words));

  // Call the appropriate `finalize()` operation to get the recovered encoded
  // message.
  switch (launder32(num_words)) {
    case kRsa2048NumWords: {
      HARDENED_CHECK_EQ(num_words, kRsa2048NumWords);
      rsa_2048_int_t recovered_message;
      HARDENED_TRY(
          rsa_modexp_finalize_size(kRsaSize2048, recovered_message.data));
      return rsa_padding_oaep_decode(
          hash_mode, label, label_bytelen, recovered_message.data,
          ARRAYSIZE(recovered_message.data), plaintext, plaintext_len);
    }
    case kRsa3072NumWords: {
      HARDENED_CHECK_EQ(num_words, kRsa3072NumWords);
      rsa_3072_int_t recovered_message;
      HARDENED_TRY(
          rsa_modexp_finalize_size(kRsaSize3072, recovered_message.data));
      return rsa_padding_oaep_decode(
          hash_mode, label, label_bytelen, recovered_message.data,
          ARRAYSIZE(recovered_message.data), plaintext, plaintext_len);
    }
    case kRsa4096NumWords: {
      HARDENED_CHECK_EQ(num_words, kRsa4096NumWords);
      rsa_4096_int_t recovered_message;
      HARDENED_TRY(
          rsa_modexp_finalize_size(kRsaSize4096, recovered_message.data));
      return rsa_padding_oaep_decode(
          hash_mode, label, label_bytelen, recovered_message.data,
          ARRAYSIZE(recovered_message.data), plaintext, plaintext_len);
    }
    default:
      // Unexpected number of words; should never get here.
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}
