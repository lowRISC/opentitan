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

status_t rsa_encrypt_start(rsa_size_t size, uint32_t e, const uint32_t *n,
                           otcrypto_key_mode_t key_mode,
                           const otcrypto_hash_mode_t hash_mode,
                           const uint8_t *message, size_t message_bytelen,
                           const uint8_t *label, size_t label_bytelen) {
  size_t num_words = 0;
  HARDENED_TRY(rsa_size_to_num_words(size, &num_words));
  HARDENED_CHECK_NE(num_words, 0);

  if (launder32(key_mode) != kOtcryptoKeyModeRsaEncryptOaep &&
      launder32(key_mode) != kOtcryptoKeyModeRsaEncryptOaepMgfSha1 &&
      launder32(key_mode) != kOtcryptoKeyModeRsaEncryptOaepMgfSha256) {
    if (launder32(hash_mode) != kOtcryptoHashModeNull || label_bytelen != 0) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeNull);
  }

  // Allocate maximum possible size to avoid VLAs. We allocate enough for
  // 4096, but will only utilize `num_words`.
  uint32_t encoded_message[kRsa4096NumWords];

  // Encode the message.
  HARDENED_TRY(hardened_memshred(encoded_message, ARRAYSIZE(encoded_message)));
  switch (launder32(key_mode)) {
    case kOtcryptoKeyModeRsaEncryptOaep:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptOaep);
      HARDENED_TRY(rsa_padding_oaep_encode(
          hash_mode, hash_mode, message, message_bytelen, label, label_bytelen,
          num_words, encoded_message));
      break;
    case kOtcryptoKeyModeRsaEncryptOaepMgfSha1:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptOaepMgfSha1);
      HARDENED_TRY(rsa_padding_oaep_encode(
          hash_mode, kOtcryptoHashModeSha1, message, message_bytelen, label,
          label_bytelen, num_words, encoded_message));
      break;
    case kOtcryptoKeyModeRsaEncryptOaepMgfSha256:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptOaepMgfSha256);
      HARDENED_TRY(rsa_padding_oaep_encode(
          hash_mode, kOtcryptoHashModeSha256, message, message_bytelen, label,
          label_bytelen, num_words, encoded_message));
      break;
    case kOtcryptoKeyModeRsaEncryptPkcs:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptPkcs);
      HARDENED_TRY(rsa_padding_pkcs1v15_encrypt_encode(
          message, message_bytelen, num_words, encoded_message));
      break;
    case kOtcryptoKeyModeRsaRaw:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaRaw);
      if (launder32(message_bytelen) != num_words * sizeof(uint32_t)) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_CHECK_EQ(message_bytelen, num_words * sizeof(uint32_t));
      HARDENED_TRY(
          randomized_bytecopy(encoded_message, message, message_bytelen));
      HARDENED_CHECK_EQ(
          consttime_memeq_byte(message, encoded_message, message_bytelen),
          kHardenedBoolTrue);
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Start computing (encoded_message ^ e) mod n with a variable-time
  // exponentiation.
  return rsa_modexp_vartime_start(size, encoded_message, e, n);
}

status_t rsa_encrypt_finalize(rsa_size_t size, uint32_t *ciphertext) {
  return rsa_modexp_finalize_size(size, ciphertext);
}

status_t rsa_decrypt_start(rsa_size_t size, const uint32_t *d0,
                           const uint32_t *d1, uint32_t e, const uint32_t *n,
                           const uint32_t *ciphertext, uint32_t checksum) {
  // Start computing (ciphertext ^ d) mod n.
  return rsa_modexp_consttime_start(size, ciphertext, d0, d1, e, n, checksum);
}

status_t rsa_decrypt_finalize(otcrypto_key_mode_t key_mode,
                              const otcrypto_hash_mode_t hash_mode,
                              const uint8_t *label, size_t label_bytelen,
                              size_t plaintext_max_bytelen, uint8_t *plaintext,
                              size_t *plaintext_len) {
  // Wait for OTBN to complete and get the size for the last RSA operation.
  size_t num_words;
  HARDENED_TRY(rsa_modexp_wait(&num_words));

  if (launder32(key_mode) != kOtcryptoKeyModeRsaEncryptOaep &&
      launder32(key_mode) != kOtcryptoKeyModeRsaEncryptOaepMgfSha1 &&
      launder32(key_mode) != kOtcryptoKeyModeRsaEncryptOaepMgfSha256) {
    if (launder32(hash_mode) != kOtcryptoHashModeNull || label_bytelen != 0) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeNull);
  }

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

  // Finalize the modexp operation to get the recovered encoded message.
  HARDENED_CHECK_LE(num_words, kRsa4096NumWords);
  uint32_t recovered_message[kRsa4096NumWords];
  HARDENED_TRY(rsa_modexp_finalize(num_words, recovered_message));

  size_t max_plaintext_bytelen = num_words * sizeof(uint32_t);
  switch (launder32(key_mode)) {
    case kOtcryptoKeyModeRsaEncryptOaep:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptOaep);
      HARDENED_TRY(rsa_padding_oaep_max_message_bytelen(
          hash_mode, num_words, &max_plaintext_bytelen));
      if (plaintext_max_bytelen < max_plaintext_bytelen) {
        return OTCRYPTO_BAD_ARGS;
      }
      return rsa_padding_oaep_decode(hash_mode, hash_mode, label, label_bytelen,
                                     recovered_message, num_words, plaintext,
                                     plaintext_len);
    case kOtcryptoKeyModeRsaEncryptOaepMgfSha1:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptOaepMgfSha1);
      HARDENED_TRY(rsa_padding_oaep_max_message_bytelen(
          hash_mode, num_words, &max_plaintext_bytelen));
      if (plaintext_max_bytelen < max_plaintext_bytelen) {
        return OTCRYPTO_BAD_ARGS;
      }
      return rsa_padding_oaep_decode(hash_mode, kOtcryptoHashModeSha1, label,
                                     label_bytelen, recovered_message,
                                     num_words, plaintext, plaintext_len);
    case kOtcryptoKeyModeRsaEncryptOaepMgfSha256:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptOaepMgfSha256);
      HARDENED_TRY(rsa_padding_oaep_max_message_bytelen(
          hash_mode, num_words, &max_plaintext_bytelen));
      if (plaintext_max_bytelen < max_plaintext_bytelen) {
        return OTCRYPTO_BAD_ARGS;
      }
      return rsa_padding_oaep_decode(hash_mode, kOtcryptoHashModeSha256, label,
                                     label_bytelen, recovered_message,
                                     num_words, plaintext, plaintext_len);
    case kOtcryptoKeyModeRsaEncryptPkcs:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaEncryptPkcs);
      return rsa_padding_pkcs1v15_decrypt_decode(recovered_message, num_words,
                                                 plaintext_max_bytelen,
                                                 plaintext, plaintext_len);
    case kOtcryptoKeyModeRsaRaw:
      HARDENED_CHECK_EQ(key_mode, kOtcryptoKeyModeRsaRaw);
      if (plaintext_max_bytelen < max_plaintext_bytelen) {
        return OTCRYPTO_BAD_ARGS;
      }
      *plaintext_len = max_plaintext_bytelen;
      HARDENED_TRY(
          randomized_bytecopy(plaintext, recovered_message, *plaintext_len));
      HARDENED_CHECK_EQ(
          consttime_memeq_byte(recovered_message, plaintext, *plaintext_len),
          kHardenedBoolTrue);
      return hardened_memshred(recovered_message, num_words);
    default:
      return OTCRYPTO_BAD_ARGS;
  }
}
