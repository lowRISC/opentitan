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

/**
 * Run GCTR on exactly one block of input.
 *
 * Updates the IV in-place.
 *
 * @param key The AES key
 * @param iv Initialization vector, 128 bits
 * @param input Input block
 * @param[out] output Output block
 */
OT_WARN_UNUSED_RESULT
static status_t gctr_process_block(const aes_key_t key, aes_block_t *iv,
                                   aes_block_t *input, aes_block_t *output) {
  HARDENED_TRY(aes_encrypt_block(key, iv, input, output));
  block_inc32(iv);
  return OTCRYPTO_OK;
}

/**
 * Implements the GCTR function as specified in SP800-38D, section 6.5.
 *
 * The block cipher is fixed to AES. Note that the GCTR function is a modified
 * version of the AES-CTR mode of encryption.
 *
 * Appends the new data to the partial data and then processes any resulting
 * full blocks. Finally, updates the partial data to hold any data that was
 * left over. The partial block may be empty, but should never be full;
 * `partial_len` should always be less than `kAesBlockNumBytes`.
 *
 * The output buffer should have enough space to hold all full blocks of
 * partial data + input data. The partial data length after this function will
 * always be `(partial_len + input_len) % kAesBlockNumBytes`.
 *
 * Updates the IV and partial block in-place; it is possible to call this
 * function again with the updated IV and partial data on additional data to
 * generate more output, and the result should be the same as if all the data
 * was passed in one call.
 *
 * @param key The AES key
 * @param iv Initialization vector, 128 bits
 * @param partial_len Length of partial block data in bytes.
 * @param partial Partial AES block.
 * @param input_len Number of bytes for input and output
 * @param input Pointer to input buffer (may be NULL if `len` is 0)
 * @param[out] output_len Number of output bytes written
 * @param[out] output Pointer to output buffer
 */
OT_WARN_UNUSED_RESULT
static status_t aes_gcm_gctr(const aes_key_t key, aes_block_t *iv,
                             size_t partial_len, aes_block_t *partial,
                             size_t input_len, const uint8_t *input,
                             size_t *output_len, uint8_t *output) {
  // Key must be intended for CTR mode.
  if (key.mode != kAesCipherModeCtr) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (input_len < kAesBlockNumBytes - partial_len) {
    // Not enough data for a full block; copy into the partial block.
    unsigned char *partial_bytes = (unsigned char *)partial->data;
    memcpy(partial_bytes + partial_len, input, input_len);
  } else {
    // Construct a block from the partial data and the start of the new data.
    unsigned char *partial_bytes = (unsigned char *)partial->data;
    memcpy(partial_bytes + partial_len, input, kAesBlockNumBytes - partial_len);
    input += kAesBlockNumBytes - partial_len;
    input_len -= kAesBlockNumBytes - partial_len;

    // Process the block.
    aes_block_t block_out;
    HARDENED_TRY(gctr_process_block(key, iv, partial, &block_out));
    memcpy(output, block_out.data, kAesBlockNumBytes);
    output += kAesBlockNumBytes;
    *output_len = kAesBlockNumBytes;

    // Process any remaining full blocks of input.
    while (input_len >= kAesBlockNumBytes) {
      memcpy(partial->data, input, kAesBlockNumBytes);
      HARDENED_TRY(gctr_process_block(key, iv, partial, &block_out));
      memcpy(output, block_out.data, kAesBlockNumBytes);
      output += kAesBlockNumBytes;
      *output_len += kAesBlockNumBytes;
      input += kAesBlockNumBytes;
      input_len -= kAesBlockNumBytes;
    }

    // Copy any remaining input into the partial block.
    memcpy(partial->data, input, input_len);
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
 * Expects the GHASH context parameter of `ctx` to represent GHASH(H, expand(A)
 * || expand(C)), where A is the aad, C is the ciphertext, and expand(x) pads x
 * to a multiple of 128 bits by adding zeroes to the right-hand side.
 *
 * @param ctx AES-GCM context
 * @param tag_len Tag length in 32-bit words
 * @param[out] tag Buffer for output tag.
 */
OT_WARN_UNUSED_RESULT
static status_t aes_gcm_get_tag(aes_gcm_context_t *ctx, size_t tag_len,
                                uint32_t *tag) {
  // Compute len64(A) and len64(C) by computing the length in *bits* (shift by
  // 3) and then converting to big-endian.
  uint64_t last_block[2] = {
      __builtin_bswap64(((uint64_t)ctx->aad_len) * 8),
      __builtin_bswap64(((uint64_t)ctx->input_len) * 8),
  };

  // Finish computing S by appending (len64(A) || len64(C)).
  ghash_update(&ctx->ghash_ctx, kAesBlockNumBytes, (unsigned char *)last_block);
  aes_block_t s;
  ghash_final(&ctx->ghash_ctx, s.data);

  // Compute the tag T = GCTR(K, J0, S).
  uint32_t full_tag[kAesBlockNumWords];
  size_t full_tag_len;
  aes_block_t empty = {.data = {0}};
  HARDENED_TRY(aes_gcm_gctr(ctx->key, &ctx->initial_counter_block,
                            /*partial_len=*/0, &empty, kAesBlockNumBytes,
                            (unsigned char *)s.data, &full_tag_len,
                            (unsigned char *)full_tag));

  // Sanity check.
  if (full_tag_len != kAesBlockNumBytes) {
    return OTCRYPTO_FATAL_ERR;
  }

  // Truncate the tag if needed. NIST requires we take the most significant
  // bits in big-endian representation, which corresponds to the least
  // significant bits in Ibex's little-endian representation.
  hardened_memcpy(tag, full_tag, tag_len);
  return OTCRYPTO_OK;
}

status_t aes_gcm_encrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t plaintext_len,
                         const uint8_t *plaintext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len,
                         uint32_t *tag, uint8_t *ciphertext) {
  aes_gcm_context_t ctx;
  HARDENED_TRY(aes_gcm_encrypt_init(key, iv_len, iv, &ctx));
  HARDENED_TRY(aes_gcm_update_aad(&ctx, aad_len, aad));
  size_t ciphertext_bytes_written;
  HARDENED_TRY(aes_gcm_update_encrypted_data(
      &ctx, plaintext_len, plaintext, &ciphertext_bytes_written, ciphertext));
  ciphertext += ciphertext_bytes_written;
  return aes_gcm_encrypt_final(&ctx, tag_len, tag, &ciphertext_bytes_written,
                               ciphertext);
}

/**
 * Starts an AES-GCM operation.
 *
 * This process is actually the same for both encryption and decryption.
 *
 * @param key Underlying AES-CTR key.
 * @param iv_len Length of the initialization vector in 32-bit words.
 * @param iv Initialization vector (nonce).
 * @param[out] ctx Initialized context object.
 * @return Error status; OK if no errors.
 */
status_t aes_gcm_init(const aes_key_t key, const size_t iv_len,
                      const uint32_t *iv, aes_gcm_context_t *ctx) {
  // Check for null pointers and IV length (must be 96 or 128 bits = 3 or 4
  // words).
  if (ctx == NULL || iv == NULL || (iv_len != 3 && iv_len != 4)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Initialize the hash subkey H.
  HARDENED_TRY(aes_gcm_hash_subkey(key, &ctx->ghash_ctx));

  // Compute the counter block (called J0 in the NIST specification).
  HARDENED_TRY(aes_gcm_counter(iv_len, iv, &ctx->ghash_ctx,
                               &ctx->initial_counter_block));

  // Set the initial IV for GCTR to inc32(J0).
  // The eventual ciphertext is C = GCTR(K, inc32(J0), plaintext).
  memcpy(ctx->gctr_iv.data, ctx->initial_counter_block.data, kAesBlockNumBytes);
  block_inc32(&ctx->gctr_iv);

  // Initialize the GHASH context. We will eventually compute
  //   S = GHASH(H, expand(A) || expand(C) || len64(A) || len64(C))
  // where:
  //   * A is the aad, C is the ciphertext
  //   * expand(x) pads x to a multiple of 128 bits by adding zeroes to the
  //     right-hand side
  //   * len64(x) is the length of x in bits expressed as a
  //     big-endian 64-bit integer.
  //
  // The tag will eventually be T = GCTR(K, J0, S).
  ghash_init(&ctx->ghash_ctx);

  // Initialize the key and lengths.
  memcpy(&ctx->key, &key, sizeof(aes_key_t));
  ctx->aad_len = 0;
  ctx->input_len = 0;

  // Zeroize the partial blocks.
  ctx->partial_ghash_block = (ghash_block_t){.data = {0}};
  ctx->partial_aes_block = (aes_block_t){.data = {0}};

  // Start in the "updating AAD" state.
  ctx->state = kAesGcmStateUpdateAad;

  return OTCRYPTO_OK;
}

status_t aes_gcm_encrypt_init(const aes_key_t key, const size_t iv_len,
                              const uint32_t *iv, aes_gcm_context_t *ctx) {
  ctx->is_encrypt = kHardenedBoolTrue;
  return aes_gcm_init(key, iv_len, iv, ctx);
}

status_t aes_gcm_update_aad(aes_gcm_context_t *ctx, const size_t aad_len,
                            const uint8_t *aad) {
  // If the length is 0, we have nothing to do.
  if (aad_len == 0) {
    return OTCRYPTO_OK;
  }

  // Check that the total AAD length is < 2^32 bytes. This is stricter than
  // NIST requires, but SP800-38D also allows implementations to stipulate
  // lower length limits.
  if (aad_len > UINT32_MAX - ctx->aad_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null pointers and ensure we are in the expected state. Once
  // we've started accumulating encrypted data, we can't add more associated
  // data because of the structure of the tag's GHASH operation.
  if (ctx == NULL || aad == NULL || ctx->state != kAesGcmStateUpdateAad) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Accumulate any full blocks of AAD into the tag's GHASH computation.
  size_t partial_ghash_block_len = ctx->aad_len % kGhashBlockNumBytes;
  ghash_process_full_blocks(&ctx->ghash_ctx, partial_ghash_block_len,
                            &ctx->partial_ghash_block, aad_len, aad);
  ctx->aad_len += aad_len;

  return OTCRYPTO_OK;
}

status_t aes_gcm_update_encrypted_data(aes_gcm_context_t *ctx, size_t input_len,
                                       const uint8_t *input, size_t *output_len,
                                       uint8_t *output) {
  // If the length is 0, we have nothing to do.
  if (input_len == 0) {
    return OTCRYPTO_OK;
  }

  // Check that the total input length is < 2^32 bytes. This is stricter
  // than NIST requires, but SP800-38D also allows implementations to stipulate
  // lower length limits.
  if (input_len > UINT32_MAX - ctx->input_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null pointers.
  if (ctx == NULL || input == NULL || output == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // If this is the first part of the plaintext, process the remaining partial
  // AAD and update the state.
  if (ctx->state == kAesGcmStateUpdateAad) {
    size_t partial_ghash_block_len = ctx->aad_len % kGhashBlockNumBytes;
    ghash_update(&ctx->ghash_ctx, partial_ghash_block_len,
                 (unsigned char *)ctx->partial_ghash_block.data);
    ctx->state = kAesGcmStateUpdateEncryptedData;
  }

  // Ensure we are in the expected state.
  if (ctx->state != kAesGcmStateUpdateEncryptedData) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Process any full blocks of input with GCTR to generate more ciphertext.
  size_t partial_aes_block_len = ctx->input_len % kAesBlockNumBytes;
  HARDENED_TRY(aes_gcm_gctr(ctx->key, &ctx->gctr_iv, partial_aes_block_len,
                            &ctx->partial_aes_block, input_len, input,
                            output_len, output));

  // Accumulate any new ciphertext to the GHASH context. The ciphertext is the
  // output for encryption, and the input for decryption.
  if (ctx->is_encrypt == kHardenedBoolTrue) {
    // Since we only generate ciphertext in full-block increments, no partial
    // blocks are possible in this case.
    if (*output_len % kGhashBlockNumBytes != 0) {
      return OTCRYPTO_RECOV_ERR;
    }
    ghash_process_full_blocks(&ctx->ghash_ctx, /*partial_len=*/0,
                              &ctx->partial_ghash_block, *output_len, output);
  } else if (ctx->is_encrypt == kHardenedBoolFalse) {
    size_t partial_ghash_block_len = ctx->input_len % kGhashBlockNumBytes;
    ghash_process_full_blocks(&ctx->ghash_ctx, partial_ghash_block_len,
                              &ctx->partial_ghash_block, input_len, input);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  ctx->input_len += input_len;
  return OTCRYPTO_OK;
}

/**
 * Finalize an AES-GCM operation: process remaining data and get the tag.
 *
 * This procedure is the same for encryption and decryption, although
 * decryption must compare the tag afterwards.
 *
 * @param ctx AES-GCM context.
 * @param tag_len Tag length in 32-bit words.
 * @param[out] tag Buffer for the tag.
 * @param[out] output_len Number of bytes written to `output`.
 * @param[out] output Buffer for output data.
 */
status_t aes_gcm_final(aes_gcm_context_t *ctx, size_t tag_len, uint32_t *tag,
                       size_t *output_len, uint8_t *output) {
  // Check for null pointers.
  if (ctx == NULL || output_len == NULL || tag == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // If there was no input (we never entered the "update encrypted data"
  // stage), process the remaining partial AAD and update the state.
  if (ctx->state == kAesGcmStateUpdateAad) {
    size_t partial_ghash_block_len = ctx->aad_len % kGhashBlockNumBytes;
    ghash_update(&ctx->ghash_ctx, partial_ghash_block_len,
                 (unsigned char *)ctx->partial_ghash_block.data);
    ctx->state = kAesGcmStateUpdateEncryptedData;
  }

  // Ensure we are in the expected state.
  if (ctx->state != kAesGcmStateUpdateEncryptedData) {
    return OTCRYPTO_BAD_ARGS;
  }

  // If a partial block of input data remains, pad it with zeroes and generate
  // one last block of output, which is then truncated to match the input
  // length.
  size_t partial_aes_block_len = ctx->input_len % kAesBlockNumBytes;
  if (partial_aes_block_len == 0) {
    *output_len = 0;
  } else {
    unsigned char *partial_aes_block_bytes =
        (unsigned char *)ctx->partial_aes_block.data;
    memset(partial_aes_block_bytes + partial_aes_block_len, 0,
           kAesBlockNumBytes - partial_aes_block_len);
    aes_block_t block_out;
    HARDENED_TRY(gctr_process_block(ctx->key, &ctx->gctr_iv,
                                    &ctx->partial_aes_block, &block_out));
    memcpy(output, block_out.data, partial_aes_block_len);
    *output_len = partial_aes_block_len;
  }

  if (ctx->is_encrypt == kHardenedBoolTrue) {
    // If a partial block of ciphertext (output for encryption) was generated,
    // accumulate in GHASH.
    if (*output_len > 0) {
      ghash_update(&ctx->ghash_ctx, *output_len, (unsigned char *)output);
    }
  } else if (ctx->is_encrypt == kHardenedBoolFalse) {
    // If a partial block of ciphertext (input for decryption) remains,
    // accumulate it in GHASH.
    size_t partial_ghash_block_len = ctx->input_len % kGhashBlockNumBytes;
    ghash_update(&ctx->ghash_ctx, partial_ghash_block_len,
                 (unsigned char *)ctx->partial_ghash_block.data);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  return aes_gcm_get_tag(ctx, tag_len, tag);
}

status_t aes_gcm_encrypt_final(aes_gcm_context_t *ctx, size_t tag_len,
                               uint32_t *tag, size_t *output_len,
                               uint8_t *output) {
  return aes_gcm_final(ctx, tag_len, tag, output_len, output);
}

status_t aes_gcm_decrypt(const aes_key_t key, const size_t iv_len,
                         const uint32_t *iv, const size_t ciphertext_len,
                         const uint8_t *ciphertext, const size_t aad_len,
                         const uint8_t *aad, const size_t tag_len,
                         const uint32_t *tag, uint8_t *plaintext,
                         hardened_bool_t *success) {
  aes_gcm_context_t ctx;
  HARDENED_TRY(aes_gcm_decrypt_init(key, iv_len, iv, &ctx));
  HARDENED_TRY(aes_gcm_update_aad(&ctx, aad_len, aad));
  size_t plaintext_bytes_written;
  HARDENED_TRY(aes_gcm_update_encrypted_data(
      &ctx, ciphertext_len, ciphertext, &plaintext_bytes_written, plaintext));
  plaintext += plaintext_bytes_written;
  return aes_gcm_decrypt_final(&ctx, tag_len, tag, &plaintext_bytes_written,
                               plaintext, success);
}

status_t aes_gcm_decrypt_init(const aes_key_t key, const size_t iv_len,
                              const uint32_t *iv, aes_gcm_context_t *ctx) {
  ctx->is_encrypt = kHardenedBoolFalse;
  return aes_gcm_init(key, iv_len, iv, ctx);
}

status_t aes_gcm_decrypt_final(aes_gcm_context_t *ctx, size_t tag_len,
                               const uint32_t *tag, size_t *output_len,
                               uint8_t *output, hardened_bool_t *success) {
  // Get the expected authentication tag.
  uint32_t expected_tag[tag_len];
  size_t bytes_written;
  HARDENED_TRY(
      aes_gcm_final(ctx, tag_len, expected_tag, &bytes_written, output));

  // Compare the expected tag to the actual tag (in constant time).
  *success = hardened_memeq(expected_tag, tag, tag_len);
  if (*success != kHardenedBoolTrue) {
    // If authentication fails, zero the plaintext so that the caller does not
    // use the unauthenticated decrypted data. We still use `OTCRYPTO_OK`
    // because there was no internal error during the authentication check.
    *success = kHardenedBoolFalse;
    memset(output, 0, bytes_written);
  }

  return OTCRYPTO_OK;
}
