// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/aes_kwp/aes_kwp.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'w', 'p')

enum {
  /** Number of bytes in a semiblock (half an AES block). */
  kSemiblockBytes = kAesBlockNumBytes / 2,
  /** Number of 32-bit words in a semiblock (half an AES block). */
  kSemiblockWords = kSemiblockBytes / sizeof(uint32_t),
};

status_t aes_kwp_wrap(const aes_key_t kek, const uint32_t *plaintext,
                      const size_t plaintext_len, uint32_t *ciphertext) {
  // The plaintext length is expected to be at most 2^32 bytes.
  if (plaintext_len > UINT32_MAX || plaintext_len == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Calculate the number of semiblocks needed for the plaintext (round up to
  // the next semiblock).
  size_t plaintext_semiblocks = ceil_div(plaintext_len, kSemiblockBytes);
  size_t pad_len = kSemiblockBytes * plaintext_semiblocks - plaintext_len;

  if (plaintext_semiblocks < 2) {
    // Plaintext is too short.
    return OTCRYPTO_BAD_ARGS;
  }

  // Load the AES block with the encryption key.
  HARDENED_TRY(aes_encrypt_begin(kek, /*iv=*/NULL));

  // This implementation follows the "indexing" method for the wrapping
  // function, as described in RFC 3394, section 2.2.1:
  //   https://datatracker.ietf.org/doc/html/rfc3394#section-2.2.1

  // Construct the first semiblock (A): a fixed 32-bit prefix followed by the
  // byte-length encoded as a big-endian 32-bit integer.
  aes_block_t block = {
      .data = {0xa65959a6, __builtin_bswap32(plaintext_len), 0, 0},
  };

  // Initialize the output buffer with (A || plaintext || padding).
  size_t plaintext_words = ceil_div(plaintext_len, sizeof(uint32_t));
  hardened_memcpy(ciphertext, block.data, kSemiblockWords);
  hardened_memcpy(ciphertext + kSemiblockWords, plaintext, plaintext_words);
  unsigned char *pad_start =
      ((unsigned char *)ciphertext) + kSemiblockBytes + plaintext_len;
  memset(pad_start, 0, pad_len);

  uint64_t t = 1;
  for (size_t j = 0; j < 6; j++) {
    for (size_t i = 1; i <= plaintext_semiblocks; i++) {
      // Copy R[i] into the block (A should already be present).
      hardened_memcpy(block.data + kSemiblockWords,
                      ciphertext + i * kSemiblockWords, kSemiblockWords);
      HARDENED_TRY(aes_update(/*dest=*/NULL, &block));
      HARDENED_TRY(aes_update(&block, /*src=*/NULL));

      // Encode the index and XOR it with the first semiblock, creating A for
      // the next iteration.
      block.data[0] ^= __builtin_bswap32((uint32_t)(t >> 32));
      block.data[1] ^= __builtin_bswap32((uint32_t)(t & UINT32_MAX));
      t++;

      // Copy the last two words back into R[i].
      hardened_memcpy(ciphertext + i * kSemiblockWords,
                      block.data + kSemiblockWords, kSemiblockWords);
    }
  }

  // Copy A into the first semiblock of the ciphertext.
  hardened_memcpy(ciphertext, block.data, kSemiblockWords);
  return OTCRYPTO_OK;
}

status_t aes_kwp_unwrap(const aes_key_t kek, const uint32_t *ciphertext,
                        const size_t ciphertext_len, hardened_bool_t *success,
                        uint32_t *plaintext) {
  // The ciphertext length is expected to be nonempty, at most 2^32 bytes, and
  // a multiple of the semiblock size.
  if (ciphertext_len > UINT32_MAX || ciphertext_len == 0 ||
      ciphertext_len % kSemiblockBytes != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Calculate the number of semiblocks.
  size_t ciphertext_semiblocks = ciphertext_len / kSemiblockBytes;

  if (ciphertext_semiblocks < 3) {
    // Ciphertext is too short.
    return OTCRYPTO_BAD_ARGS;
  }

  // Load the AES block with the decryption key.
  HARDENED_TRY(aes_decrypt_begin(kek, /*iv=*/NULL));

  // This implementation follows the "indexing" method for the wrapping
  // function, as described in RFC 3394, section 2.2.2:
  //   https://datatracker.ietf.org/doc/html/rfc3394#section-2.2.2

  // Set the first semiblock, A.
  aes_block_t block = {
      .data = {ciphertext[0], ciphertext[1], 0, 0},
  };

  // Initialize the working buffer, R.
  uint32_t r[(ciphertext_semiblocks - 1) * kSemiblockWords];
  hardened_memcpy(r, ciphertext + kSemiblockWords, ARRAYSIZE(r));

  uint64_t t = 6 * ((uint64_t)ciphertext_semiblocks - 1);
  for (size_t j = 0; j < 6; j++) {
    for (size_t i = ciphertext_semiblocks - 1; 1 <= i; i--) {
      // Encode the index and XOR it with the first semiblock (A ^ t).
      block.data[0] ^= __builtin_bswap32((uint32_t)(t >> 32));
      block.data[1] ^= __builtin_bswap32((uint32_t)(t & UINT32_MAX));
      t--;

      // Copy R[i] into the block (A ^ t should already be present).
      hardened_memcpy(block.data + kSemiblockWords,
                      r + (i - 1) * kSemiblockWords, kSemiblockWords);
      HARDENED_TRY(aes_update(/*dest=*/NULL, &block));
      HARDENED_TRY(aes_update(&block, /*src=*/NULL));

      // Copy the last two words back into R[i].
      hardened_memcpy(r + (i - 1) * kSemiblockWords,
                      block.data + kSemiblockWords, kSemiblockWords);
    }
  }

  // Check that the first 32 bits of A match the AES-KWP fixed prefix.
  if (block.data[0] != 0xa65959a6) {
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Decode the next 32 bits of A as the plaintext length.
  size_t plaintext_len = __builtin_bswap32(block.data[1]);
  size_t pad_len =
      kSemiblockBytes * (ciphertext_semiblocks - 1) - plaintext_len;

  // Check that the padding length is valid.
  if (pad_len >= kSemiblockBytes) {
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Check that the padding bytes are zero. Note: this should happen only after
  // the prefix check. Otherwise it could expose a padding oracle, because
  // memcmp is not constant-time.
  if (pad_len != 0) {
    uint8_t exp_pad[pad_len];
    memset(exp_pad, 0, pad_len);
    unsigned char *pad_start = ((unsigned char *)r) + plaintext_len;
    if (memcmp(pad_start, exp_pad, pad_len) != 0) {
      *success = kHardenedBoolFalse;
      return OTCRYPTO_OK;
    }
  }

  // Copy the plaintext into the destination buffer.
  size_t plaintext_words = ceil_div(plaintext_len, sizeof(uint32_t));
  hardened_memcpy(plaintext, r, plaintext_words);

  // Return success.
  *success = kHardenedBoolTrue;
  return OTCRYPTO_OK;
}
