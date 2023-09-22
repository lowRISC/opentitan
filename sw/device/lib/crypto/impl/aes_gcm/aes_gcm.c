// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('g', 'c', 'm')

enum {
  /**
   * Log2 of the number of bytes in an AES block.
   */
  kAesBlockLog2NumBytes = 4,
};
static_assert(kAesBlockNumBytes == (1 << kAesBlockLog2NumBytes),
              "kAesBlockLog2NumBytes does not match kAesBlockNumBytes");

/**
 * Increment a 32-bit big-endian word.
 *
 * This operation theoretically increments the "rightmost" (last) 32 bits of
 * the input modulo 2^32. However, NIST treats all bitvectors as big-endian and
 * the processor is little-endian. In order to increment we first need to
 * reverse the bytes of the 32-bit word, then increment, then reverse it back.
 *
 * @param word Input word in big-endian form.
 * @returns (word + 1) mod 2^32 in big-endian form.
 */
static inline uint32_t word_inc32(const uint32_t word) {
  // Reverse the bytes, increment, and reverse back.
  return __builtin_bswap32(__builtin_bswap32(word) + 1);
}

/**
 * Implements the inc32() function on blocks from NIST SP800-38D.
 *
 * Interprets the last (rightmost) 32 bits of the block as a big-endian integer
 * and increments this value modulo 2^32 in-place.
 *
 * @param block AES block, modified in place.
 */
static inline void block_inc32(aes_block_t *block) {
  // Set the last word to the incremented value.
  block->data[kAesBlockNumWords - 1] =
      word_inc32(block->data[kAesBlockNumWords - 1]);
}

/**
 * One-shot version of the AES encryption API for a single block.
 */
OT_WARN_UNUSED_RESULT
static status_t aes_encrypt_block(const aes_key_t key, const aes_block_t *iv,
                                  const aes_block_t *input,
                                  aes_block_t *output) {
  HARDENED_TRY(aes_encrypt_begin(key, iv));
  HARDENED_TRY(aes_update(/*dest=*/NULL, input));
  HARDENED_TRY(aes_update(output, /*src=*/NULL));
  return aes_end(NULL);
}

status_t aes_gcm_gctr(const aes_key_t key, const aes_block_t *icb, size_t len,
                      const uint8_t *input, uint8_t *output) {
  // If the input is empty, the output must be as well. Since the output length
  // is 0, simply return.
  if (len == 0) {
    return OTCRYPTO_OK;
  }

  // NULL pointers are not allowed for nonzero input length.
  if (input == NULL || output == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // TODO: add support for sideloaded keys.
  if (key.sideload != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Key must be intended for CTR mode.
  if (key.mode != kAesCipherModeCtr) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Initial IV = ICB.
  aes_block_t iv;
  memcpy(iv.data, icb->data, kAesBlockNumBytes);

  // Process the input one block at a time.
  while (len > 0) {
    aes_block_t block_in;
    size_t nbytes = kAesBlockNumBytes;
    if (len < kAesBlockNumBytes) {
      // Last block is partial; copy the bytes that exist and set the rest of
      // the block to 0.
      memset(block_in.data, 0, kAesBlockNumBytes);
      nbytes = len;
    }
    memcpy(block_in.data, input, nbytes);
    len -= nbytes;
    input += nbytes;

    // Run the AES-CTR encryption operation on the next block of input.
    aes_block_t block_out;
    HARDENED_TRY(aes_encrypt_block(key, &iv, &block_in, &block_out));

    // Copy the result block into the output buffer, truncating some bytes if
    // the input block was partial.
    memcpy(output, block_out.data, nbytes);
    output += nbytes;

    // Update the counter block with inc32().
    block_inc32(&iv);
  }

  return OTCRYPTO_OK;
}

/**
 * Verify that the lengths of AES-GCM parameters are acceptable.
 *
 * This routine can be used for both authenticated encryption and authenticated
 * decryption; the lengths of the plaintext and ciphertext always match, and
 * `plaintext_len` may represent either.
 *
 * @param iv_len IV length in 32-bit words
 * @param plaintext_len Plaintext/ciphertext length in bytes
 * @param aad_len Associated data length in bytes
 * @return `OTCRYPTO_OK` if the lengths are OK, and `OTCRYPTO_BAD_ARGS`
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
static status_t check_buffer_lengths(const size_t iv_len,
                                     const size_t plaintext_len,
                                     const size_t aad_len) {
  // Check IV length (must be 96 or 128 bits = 3 or 4 words).
  if (iv_len != 3 && iv_len != 4) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check plaintext/AAD length. Both must be less than 2^32 bytes long. This
  // is stricter than NIST requires, but SP800-38D also allows implementations
  // to stipulate lower length limits.
  if (plaintext_len > UINT32_MAX || aad_len > UINT32_MAX) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Compute and set the hash subkey for AES-GCM.
 *
 * If any step in this process fails, the function returns an error and the
 * output should not be used.
 *
 * @param key AES key
 * @param[out] ctx Destination GHASH context object
 * @return OK or error
 */
OT_WARN_UNUSED_RESULT
static status_t aes_gcm_hash_subkey(const aes_key_t key, ghash_context_t *ctx) {
  // Compute the initial hash subkey H = AES_K(0). Note that to get this
  // result from AES_CTR, we set both the IV and plaintext to zero; this way,
  // AES-CTR's final XOR with the plaintext does nothing.
  aes_block_t zero;
  memset(zero.data, 0, kAesBlockNumBytes);
  aes_block_t hash_subkey;
  HARDENED_TRY(aes_encrypt_block(key, &zero, &zero, &hash_subkey));

  // Set the key for the GHASH context.
  ghash_init_subkey(hash_subkey.data, ctx);

  return OTCRYPTO_OK;
}

/**
 * Compute the counter block based on the given IV and hash subkey.
 *
 * This block is called J0 in the NIST documentation, and is the same for both
 * encryption and decryption.
 *
 * @param iv_len IV length in 32-bit words
 * @param iv IV value
 * @param ctx GHASH context with product table for hash subkey H
 * @param[out] j0 Destination for the output counter block
 * @return OK or error
 */
OT_WARN_UNUSED_RESULT
static status_t aes_gcm_counter(const size_t iv_len, const uint32_t *iv,
                                ghash_context_t *ctx, aes_block_t *j0) {
  if (iv_len == 3) {
    // If the IV is 96 bits, then J0 = (IV || {0}^31 || 1).
    hardened_memcpy(j0->data, iv, iv_len);
    // Set the last word to 1 (as a big-endian integer).
    j0->data[kAesBlockNumWords - 1] = __builtin_bswap32(1);
  } else if (iv_len == 4) {
    // If the IV is 128 bits, then J0 = GHASH(H, IV || {0}^120 || 0x80), where
    // {0}^120 means 120 zero bits (15 0x00 bytes).
    ghash_init(ctx);
    ghash_update(ctx, iv_len * sizeof(uint32_t), (unsigned char *)iv);
    uint8_t buffer[kAesBlockNumBytes];
    memset(buffer, 0, kAesBlockNumBytes);
    buffer[kAesBlockNumBytes - 1] = 0x80;
    ghash_update(ctx, kAesBlockNumBytes, buffer);
    ghash_final(ctx, j0->data);
  } else {
    // Should not happen; invalid IV length.
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

/**
 * Compute the AES-GCM authentication tag.
 *
 * @param key AES key
 * @param ctx GHASH context with precomputed table for hash subkey H
 * @param ciphertext_len Length of the ciphertext in bytes
 * @param ciphertext Ciphertext value
 * @param aad_len Length of the associated data in bytes
 * @param aad Associated data value
 * @param j0 Counter block (J0 in the NIST specification)
 * @param tag_len Tag length in bytes
 * @param[out] tag Buffer for output tag (128 bits)
 */
OT_WARN_UNUSED_RESULT
static status_t aes_gcm_compute_tag(const aes_key_t key, ghash_context_t *ctx,
                                    const size_t ciphertext_len,
                                    const uint8_t *ciphertext,
                                    const size_t aad_len, const uint8_t *aad,
                                    const aes_block_t *j0, size_t tag_len,
                                    uint8_t *tag) {
  // Compute S = GHASH(H, expand(A) || expand(C) || len64(A) || len64(C))
  // where:
  //   * A is the aad, C is the ciphertext
  //   * expand(x) pads x to a multiple of 128 bits by adding zeroes to the
  //     right-hand side
  //   * len64(x) is the length of x in bits expressed as a
  //     big-endian 64-bit integer.

  // Compute GHASH(H, expand(A) || expand(C)).
  ghash_init(ctx);
  ghash_update(ctx, aad_len, aad);
  ghash_update(ctx, ciphertext_len, ciphertext);

  // Compute len64(A) and len64(C) by computing the length in *bits* (shift by
  // 3) and then converting to big-endian.
  uint64_t last_block[2] = {
      __builtin_bswap64(((uint64_t)aad_len) * 8),
      __builtin_bswap64(((uint64_t)ciphertext_len) * 8),
  };

  // Finish computing S by appending (len64(A) || len64(C)).
  ghash_update(ctx, kAesBlockNumBytes, (unsigned char *)last_block);
  aes_block_t s;
  ghash_final(ctx, s.data);

  // Compute the tag T = GCTR(K, J0, S).
  uint32_t full_tag[kAesBlockNumWords];
  HARDENED_TRY(aes_gcm_gctr(key, j0, kAesBlockNumBytes, (unsigned char *)s.data,
                            (unsigned char *)full_tag));

  // Truncate the tag if needed. NIST requires we take the most significant
  // bits in big-endian representation, which corresponds to the least
  // significant bits in Ibex's little-endian representation.
  memcpy(tag, full_tag, tag_len);

  return OTCRYPTO_OK;
}

status_t aes_gcm_encrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t plaintext_len,
                         const uint8_t *plaintext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len, uint8_t *tag,
                         uint8_t *ciphertext) {
  // Check that the input parameter sizes are valid.
  HARDENED_TRY(check_buffer_lengths(iv_len, plaintext_len, aad_len));

  // Initialize the hash subkey H.
  ghash_context_t ctx;
  HARDENED_TRY(aes_gcm_hash_subkey(key, &ctx));

  // Compute the counter block (called J0 in the NIST specification).
  aes_block_t j0;
  HARDENED_TRY(aes_gcm_counter(iv_len, iv, &ctx, &j0));

  // Compute inc32(J0).
  aes_block_t j0_inc;
  memcpy(j0_inc.data, j0.data, kAesBlockNumBytes);
  block_inc32(&j0_inc);

  // Compute ciphertext C = GCTR(K, inc32(J0), plaintext).
  HARDENED_TRY(
      aes_gcm_gctr(key, &j0_inc, plaintext_len, plaintext, ciphertext));

  // Compute the authentication tag T.
  return aes_gcm_compute_tag(key, &ctx, plaintext_len, ciphertext, aad_len, aad,
                             &j0, tag_len, tag);
}

status_t aes_gcm_decrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t ciphertext_len,
                         const uint8_t *ciphertext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len,
                         const uint8_t *tag, uint8_t *plaintext,
                         hardened_bool_t *success) {
  // Check that the input parameter sizes are valid.
  HARDENED_TRY(check_buffer_lengths(iv_len, ciphertext_len, aad_len));

  // Get the tag length in words.
  if (tag_len % sizeof(uint32_t) != 0) {
    // Tag length must be a multiple of 32 bits.
    return OTCRYPTO_BAD_ARGS;
  }
  size_t tag_len_words = tag_len / sizeof(uint32_t);

  // Initialize the hash subkey H.
  ghash_context_t ctx;
  HARDENED_TRY(aes_gcm_hash_subkey(key, &ctx));

  // Compute the counter block (called J0 in the NIST specification).
  aes_block_t j0;
  HARDENED_TRY(aes_gcm_counter(iv_len, iv, &ctx, &j0));

  // Compute the expected authentication tag T.
  uint32_t expected_tag[tag_len_words];
  HARDENED_TRY(aes_gcm_compute_tag(key, &ctx, ciphertext_len, ciphertext,
                                   aad_len, aad, &j0, tag_len,
                                   (unsigned char *)expected_tag));

  // Copy actual tag to word-size buffers to ensure it is aligned for
  // `hardened_memeq`.
  uint32_t tag_words[tag_len_words];
  memcpy(tag_words, tag, tag_len);

  // Compare the expected tag to the actual tag (in constant time).
  *success = hardened_memeq(expected_tag, tag_words, tag_len_words);
  if (*success != kHardenedBoolTrue) {
    // If authentication fails, do not proceed to decryption; simply exit
    // with success = False. We still use `OTCRYPTO_OK` because there was no
    // internal error during the authentication check.
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Compute plaintext P = GCTR(K, inc32(J0), ciphertext).
  block_inc32(&j0);
  return aes_gcm_gctr(key, &j0, ciphertext_len, ciphertext, plaintext);
}
