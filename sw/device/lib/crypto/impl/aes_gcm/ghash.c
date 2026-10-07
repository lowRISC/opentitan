// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('g', 'h', 'a')

enum {
  /**
   * Log2 of the number of bytes in an AES block.
   */
  kGhashBlockLog2NumBytes = 4,
  /**
   * Low terms of the field modulus, x^7 + x^2 + x + 1, as a polynomial in the
   * bit order of the carry-less multiplication.
   *
   * The field modulus for GCM is x^128 + x^7 + x^2 + x + 1, so x^128 is
   * congruent to these terms.
   */
  kGhashReduceTerms = 0x87,
};
static_assert(kGhashBlockNumBytes == (1 << kGhashBlockLog2NumBytes),
              "kGhashBlockLog2NumBytes does not match kGhashBlockNumBytes");

/**
 * Performs a bitwise XOR of two blocks.
 *
 * This operation corresponds to addition in the Galois field.
 *
 * @param x First operand block
 * @param y Second operand block
 * @param[out] out Buffer in which to store output; can be the same as one or
 * both operands.
 */
static inline void block_xor(const ghash_block_t *x, const ghash_block_t *y,
                             ghash_block_t *out) {
  for (size_t i = 0; i < kGhashBlockNumWords; ++i) {
    out->data[i] = x->data[i] ^ y->data[i];
  }
}

/**
 * Reverse the order of the bits within each byte of a word.
 *
 * GCM numbers the coefficients of a block from the most significant bit of
 * its first byte. The carry-less multiplication numbers them from the least
 * significant bit of a word. With the bits of each byte reversed, bit i of
 * word j of a block is the coefficient of x^(32j + i).
 *
 * @param word Input word.
 * @return Word with the bits of each byte reversed.
 */
static uint32_t reverse_bits_in_bytes(uint32_t word) {
  word = ((word >> 1) & 0x55555555) | ((word & 0x55555555) << 1);
  word = ((word >> 2) & 0x33333333) | ((word & 0x33333333) << 2);
  return ((word >> 4) & 0x0f0f0f0f) | ((word & 0x0f0f0f0f) << 4);
}

/**
 * Reverse the order of the bits within each byte of a block.
 *
 * Converts a block between the bit order of GCM and the bit order of the
 * carry-less multiplication, in either direction.
 *
 * @param[in,out] block Block to convert.
 */
static void block_reverse_bits_in_bytes(ghash_block_t *block) {
  for (size_t i = 0; i < kGhashBlockNumWords; ++i) {
    block->data[i] = reverse_bits_in_bytes(block->data[i]);
  }
}

/**
 * Add the carry-less product of two words to two words of an accumulator.
 *
 * The low word of the 64-bit product is added to `lo` and the high word to
 * `hi`.
 *
 * Runs in constant time.
 *
 * This function must be inlined, so that the accumulator words stay in
 * registers. With Zbc, both multiplications and both additions are in one
 * `volatile` block, so the compiler keeps the steps in program order and adds
 * each product right away. Computing all products first would leave more
 * values live than there are registers, and some would be spilled to the
 * stack.
 *
 * @param lhs First operand.
 * @param rhs Second operand.
 * @param[in,out] lo Accumulator word for the low word of the product.
 * @param[in,out] hi Accumulator word for the high word of the product.
 */
OT_ALWAYS_INLINE
static void clmul_add(uint32_t lhs, uint32_t rhs, uint32_t *lo, uint32_t *hi) {
#ifdef __riscv_zbc
  uint32_t product;
  asm volatile(
      "clmul %[product], %[lhs], %[rhs]\n"
      "xor %[lo], %[lo], %[product]\n"
      "clmulh %[product], %[lhs], %[rhs]\n"
      "xor %[hi], %[hi], %[product]"
      : [lo] "+&r"(*lo), [hi] "+r"(*hi), [product] "=&r"(product)
      : [lhs] "r"(lhs), [rhs] "r"(rhs));
#else
  for (size_t i = 0; i < 32; ++i) {
    *lo ^= (lhs << i) & (0 - ((rhs >> i) & 1));
  }
  for (size_t i = 1; i < 32; ++i) {
    *hi ^= (lhs >> (32 - i)) & (0 - ((rhs >> i) & 1));
  }
#endif
}

/**
 * Multiply an accumulator by x^32 and add the product of a word and the hash
 * subkey.
 *
 * This is one step of Horner's rule over the words of the state. The word that
 * moves above x^127 is reduced right away, so the accumulator never grows
 * beyond four words. This leaves few enough live values that the compiler
 * keeps all of them in registers, with or without Zbc.
 *
 * This function must be inlined, for the same reason as `clmul_add`.
 *
 * @param word State word, in the bit order of the carry-less multiplication.
 * @param hash_subkey Masked hash subkey share, as set by `ghash_init_subkey`.
 * @param[in,out] acc Accumulator, in the same bit order.
 */
OT_ALWAYS_INLINE
static void mul_x32_add(uint32_t word, const ghash_block_t *hash_subkey,
                        ghash_block_t *acc) {
  uint32_t top = acc->data[3];
  acc->data[3] = acc->data[2];
  acc->data[2] = acc->data[1];
  acc->data[1] = acc->data[0];
  acc->data[0] = 0;
  clmul_add(word, hash_subkey->data[0], &acc->data[0], &acc->data[1]);
  clmul_add(word, hash_subkey->data[1], &acc->data[1], &acc->data[2]);
  clmul_add(word, hash_subkey->data[2], &acc->data[2], &acc->data[3]);
  clmul_add(word, hash_subkey->data[3], &acc->data[3], &top);
  // x^128 is congruent to `kGhashReduceTerms`, so the top word is reduced by
  // multiplying it with those terms. The product fits in the two low words.
  clmul_add(top, kGhashReduceTerms, &acc->data[0], &acc->data[1]);
}

uint32_t ghash_context_integrity_checksum(const ghash_context_t *ghash_ctx) {
  uint32_t ctx;
  crc32_init(&ctx);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)&ghash_ctx->hash_subkey0,
            sizeof(ghash_ctx->hash_subkey0));
  crc32_add(&ctx, (unsigned char *)&ghash_ctx->correction_term0,
            sizeof(ghash_ctx->correction_term0));
  crc32_add(&ctx, (unsigned char *)&ghash_ctx->enc_initial_counter_block0,
            sizeof(ghash_ctx->enc_initial_counter_block0));
  // Note that we do not calculate the crc over the state.
  return crc32_finish(&ctx);
}

hardened_bool_t ghash_context_integrity_checksum_check(
    const ghash_context_t *ghash_ctx) {
  if (ghash_ctx->checksum ==
      launder32(ghash_context_integrity_checksum(ghash_ctx))) {
    return kHardenedBoolTrue;
  }
  return kHardenedBoolFalse;
}

status_t ghash_init_subkey(const uint32_t *hash_subkey, ghash_block_t *subkey) {
  for (size_t i = 0; i < kGhashBlockNumWords; ++i) {
    subkey->data[i] = reverse_bits_in_bytes(hash_subkey[i]);
  }
  return OTCRYPTO_OK;
}

status_t ghash_init(ghash_context_t *ctx) {
  // Randomize the initial state.
  hardened_memshred(ctx->state0.data, kGhashBlockNumWords);
  hardened_memshred(ctx->state1.data, kGhashBlockNumWords);
  // Initialize the ghash block counter.
  ctx->ghash_block_cnt = 0;

  ctx->checksum = ghash_context_integrity_checksum(ctx);

  return LAUNDERED_OTCRYPTO_OK;
}

/**
 * Multiply the GHASH state by a hash subkey share.
 *
 * See NIST SP800-38D, section 6.3.
 *
 * This operation corresponds to multiplication in the Galois field with order
 * 2^128, modulo the polynomial x^128 + x^7 + x^2 + x + 1. The state, the
 * subkey and the result are in the bit order of the carry-less multiplication
 * (see `reverse_bits_in_bytes`), so they need no conversion here.
 *
 * The product is written through `result` instead of being returned, so that
 * no unshredded copy of it is left in the caller's stack frame. The register
 * file is cleared before returning, so that no value derived from one subkey
 * share is still in a register when the next multiplication loads the
 * corresponding value of the other share.
 *
 * @param state GHASH state.
 * @param hash_subkey Masked hash subkey share, as set by `ghash_init_subkey`.
 * @param[out] result Multiplication of the state and the hash subkey. It must
 * not overlap `state` or `hash_subkey`.
 */
static void galois_mul_state_key(const ghash_block_t *state,
                                 const ghash_block_t *hash_subkey,
                                 ghash_block_t *result) {
  // Horner's rule over the state words a0 to a3, from the most significant:
  // ((a3 * H * x^32 + a2 * H) * x^32 + a1 * H) * x^32 + a0 * H.
  ghash_block_t acc = {.data = {0}};
  mul_x32_add(state->data[3], hash_subkey, &acc);
  mul_x32_add(state->data[2], hash_subkey, &acc);
  mul_x32_add(state->data[1], hash_subkey, &acc);
  mul_x32_add(state->data[0], hash_subkey, &acc);

  result->data[0] = acc.data[0];
  result->data[1] = acc.data[1];
  result->data[2] = acc.data[2];
  result->data[3] = acc.data[3];

  ibex_clear_rf();
}

/**
 * Overwrite a GHASH block with random data; used as a cleanup guard.
 *
 * @param block GHASH block to shred.
 */
static void ghash_block_shred(ghash_block_t *block) {
  hardened_memshred(block->data, kGhashBlockNumWords);
}

/**
 * Overwrite a GHASH context with random data; used as a cleanup guard.
 *
 * @param ctx GHASH context to shred.
 */
static void ghash_context_shred(ghash_context_t *ctx) {
  hardened_memshred((uint32_t *)ctx,
                    sizeof(ghash_context_t) / sizeof(uint32_t));
}

/**
 * Temporaries of the single-block update.
 *
 * Each block overwrites the previous block's values, so the caller shreds them
 * once after its last block instead of after every block.
 */
typedef struct ghash_scratch {
  /**
   * Later blocks: the block XORed with both state shares.
   */
  ghash_block_t tmp;
  /**
   * First block: share 0 input. Later blocks: share 0 product.
   */
  ghash_block_t s0_tmp;
  /**
   * First block: share 1 input. Later blocks: share 1 product.
   */
  ghash_block_t s1_tmp;
} ghash_scratch_t;

/**
 * Overwrite GHASH temporaries with random data; used as a cleanup guard.
 *
 * @param scratch Temporaries to shred.
 */
static void ghash_scratch_shred(ghash_scratch_t *scratch) {
  hardened_memshred((uint32_t *)scratch,
                    sizeof(ghash_scratch_t) / sizeof(uint32_t));
}

/**
 * Refreshes the randomness used to mask the GHASH hash subkey shares.
 *
 * Shifts both subkey shares H0 and H1 by a fresh random delta mask, updating
 * the correction terms in-place.
 */
OT_WARN_UNUSED_RESULT
static status_t ghash_refresh_subkey_mask(ghash_context_t *ctx) {
  // Check that the context's checksum is correct before modifying.
  HARDENED_CHECK_EQ(ghash_context_integrity_checksum_check(ctx),
                    kHardenedBoolTrue);

  ghash_block_t delta_h __attribute__((cleanup(ghash_block_shred)));
  HARDENED_TRY(hardened_memshred(delta_h.data, kGhashBlockNumWords));

  ghash_block_t subkey_delta __attribute__((cleanup(ghash_block_shred)));
  HARDENED_TRY(ghash_init_subkey(delta_h.data, &subkey_delta));

  // Update both hash subkey shares with subkey_delta.
  block_xor(&ctx->hash_subkey0, &subkey_delta, &ctx->hash_subkey0);
  block_xor(&ctx->hash_subkey1, &subkey_delta, &ctx->hash_subkey1);

  // Update correction_term0 and correction_term1 (both shifted by S0 *
  // delta_h).
  ghash_block_t s0_delta __attribute__((cleanup(ghash_block_shred)));
  galois_mul_state_key(&ctx->enc_initial_counter_block0, &subkey_delta,
                       &s0_delta);
  block_xor(&ctx->correction_term0, &s0_delta, &ctx->correction_term0);
  block_xor(&ctx->correction_term1, &s0_delta, &ctx->correction_term1);

  // Update correction_term1_init (shifted by S1 * delta_h).
  ghash_block_t s1_delta __attribute__((cleanup(ghash_block_shred)));
  galois_mul_state_key(&ctx->enc_initial_counter_block1, &subkey_delta,
                       &s1_delta);
  block_xor(&ctx->correction_term1_init, &s1_delta,
            &ctx->correction_term1_init);

  // Recompute the structure checksum after modifying the subkey shares and
  // correction terms.
  ctx->checksum = ghash_context_integrity_checksum(ctx);

  return OTCRYPTO_OK;
}

/**
 * Single-block update function for GHASH.
 *
 * @param ctx GHASH context.
 * @param block Block to incorporate.
 * @param scratch Temporaries, shredded by the caller.
 */
static status_t ghash_process_block(ghash_context_t *ctx, ghash_block_t *block,
                                    ghash_scratch_t *scratch) {
  // Periodically refresh the subkey mask every 64 blocks to limit
  // side-channel DPA/CPA trace accumulation on long messages.
  if (ctx->ghash_block_cnt > 0 && (ctx->ghash_block_cnt % 64) == 0) {
    HARDENED_TRY(ghash_refresh_subkey_mask(ctx));
  }

  if (ctx->ghash_block_cnt == 0) {
    // Process share 0.
    // share0_tmp = (S0 + T0) * H0
    hardened_memcpy(scratch->s0_tmp.data, block->data, kGhashBlockNumWords);
    block_reverse_bits_in_bytes(&scratch->s0_tmp);
    hardened_xor_in_place(scratch->s0_tmp.data,
                          ctx->enc_initial_counter_block0.data,
                          kGhashBlockNumWords);
    galois_mul_state_key(&scratch->s0_tmp, &ctx->hash_subkey0, &ctx->state0);

    // Apply the correction terms for state share 0.
    // share0 = share0_tmp + (S0*(H0+1))
    hardened_xor_in_place(ctx->state0.data, ctx->correction_term0.data,
                          kGhashBlockNumWords);

    // Clear the RF before operating on the second share to avoid leakage
    // between both shares.
    ibex_clear_rf();

    // Process share 1.
    // share1_tmp = (S1 + T0) * H1
    hardened_memcpy(scratch->s1_tmp.data, block->data, kGhashBlockNumWords);
    block_reverse_bits_in_bytes(&scratch->s1_tmp);
    hardened_xor_in_place(scratch->s1_tmp.data,
                          ctx->enc_initial_counter_block1.data,
                          kGhashBlockNumWords);
    ibex_clear_rf();
    galois_mul_state_key(&scratch->s1_tmp, &ctx->hash_subkey1, &ctx->state1);

    // Apply the correction terms for state share 1.
    // share1 = share1_tmp + correction_term1
    hardened_xor_in_place(ctx->state1.data, ctx->correction_term1_init.data,
                          kGhashBlockNumWords);
  } else {
    // Process share 0.
    // tmp = (share0+TN-1)+share1
    hardened_memcpy(scratch->tmp.data, block->data, kGhashBlockNumWords);
    block_reverse_bits_in_bytes(&scratch->tmp);
    hardened_xor_in_place(scratch->tmp.data, ctx->state0.data,
                          kGhashBlockNumWords);
    hardened_xor_in_place(scratch->tmp.data, ctx->state1.data,
                          kGhashBlockNumWords);

    // s0_tmp = tmp * H0
    galois_mul_state_key(&scratch->tmp, &ctx->hash_subkey0, &scratch->s0_tmp);

    // Apply the correction terms for state share 0.
    // share0 = share0_tmp + (S0*(H0+1))
    ibex_clear_rf();
    hardened_memcpy(ctx->state0.data, scratch->s0_tmp.data,
                    kGhashBlockNumWords);
    hardened_xor_in_place(ctx->state0.data, ctx->correction_term0.data,
                          kGhashBlockNumWords);

    // Process share 1.
    // share1_tmp = tmp * H1
    ibex_clear_rf();
    galois_mul_state_key(&scratch->tmp, &ctx->hash_subkey1, &scratch->s1_tmp);

    // Apply the correction terms for state share 1.
    // share1 = share1_tmp + (S0*H0)
    hardened_memcpy(ctx->state1.data, scratch->s1_tmp.data,
                    kGhashBlockNumWords);
    hardened_xor_in_place(ctx->state1.data, ctx->correction_term1.data,
                          kGhashBlockNumWords);
  }

  // Check that the context's checksum is correct.
  HARDENED_CHECK_EQ(ghash_context_integrity_checksum_check(ctx),
                    kHardenedBoolTrue);

  // Increment the number of processed ghash block counter.
  ctx->ghash_block_cnt++;

  return LAUNDERED_OTCRYPTO_OK;
}

/**
 * Version of `ghash_process_full_blocks` that uses the caller's temporaries.
 *
 * @param ctx Context object.
 * @param partial_len Length of the partial block.
 * @param partial Partial GHASH block.
 * @param input_buf Input data buffer.
 * @param scratch Temporaries, shredded by the caller.
 */
OT_WARN_UNUSED_RESULT
static status_t process_full_blocks(ghash_context_t *ctx, size_t partial_len,
                                    ghash_block_t *partial,
                                    const otcrypto_const_byte_buf_t *input_buf,
                                    ghash_scratch_t *scratch) {
  size_t input_len = input_buf->len;
  const uint8_t *input = input_buf->data;
  if (input_len < kGhashBlockNumBytes - partial_len) {
    // Not enough data for a full block; copy into the partial block.
    unsigned char *partial_bytes = (unsigned char *)partial->data;
    randomized_bytecopy(partial_bytes + partial_len, input, input_len);
  } else {
    // Construct a block from the partial data and the start of the new data.
    unsigned char *partial_bytes = (unsigned char *)partial->data;
    randomized_bytecopy(partial_bytes + partial_len, input,
                        kGhashBlockNumBytes - partial_len);
    input += kGhashBlockNumBytes - partial_len;
    input_len -= kGhashBlockNumBytes - partial_len;

    // Process the block.
    HARDENED_TRY(ghash_process_block(ctx, partial, scratch));

    // Process any remaining full blocks of input.
    while (input_len >= kGhashBlockNumBytes) {
      randomized_bytecopy(partial->data, input, kGhashBlockNumBytes);
      HARDENED_TRY(ghash_process_block(ctx, partial, scratch));
      input += kGhashBlockNumBytes;
      input_len -= kGhashBlockNumBytes;
    }

    // Copy any remaining input into the partial block.
    randomized_bytecopy(partial->data, input, input_len);
  }

  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(input_buf));

  return OTCRYPTO_OK;
}

status_t ghash_process_full_blocks(ghash_context_t *ctx, size_t partial_len,
                                   ghash_block_t *partial,
                                   const otcrypto_const_byte_buf_t *input_buf) {
  ghash_scratch_t scratch __attribute__((cleanup(ghash_scratch_shred)));
  return process_full_blocks(ctx, partial_len, partial, input_buf, &scratch);
}

status_t ghash_update(ghash_context_t *ctx,
                      const otcrypto_const_byte_buf_t *input) {
  ghash_scratch_t scratch __attribute__((cleanup(ghash_scratch_shred)));

  // Process all full blocks and write the remaining non-full data into
  // `partial`.
  ghash_block_t partial = {.data = {0}};
  HARDENED_TRY(process_full_blocks(ctx, 0, &partial, input, &scratch));

  // Check if there is data remaining, and process it if so.
  size_t partial_len = input->len % kGhashBlockNumBytes;
  if (partial_len != 0) {
    unsigned char *partial_bytes = (unsigned char *)partial.data;
    memset(partial_bytes + partial_len, 0, kGhashBlockNumBytes - partial_len);
    HARDENED_TRY(ghash_process_block(ctx, &partial, &scratch));
  }

  return OTCRYPTO_OK;
}

status_t ghash_update_redundant(ghash_context_t *ctx,
                                const otcrypto_const_byte_buf_t *input) {
  // Copy ctx.
  ghash_context_t ctx_redundant __attribute__((cleanup(ghash_context_shred)));
  randomized_bytecopy(&ctx_redundant, ctx, sizeof(ctx_redundant));

  HARDENED_TRY(ghash_update(ctx, input));

  ghash_update(&ctx_redundant, input);

  // Compare state0_reg ^ state0_red == state1_reg ^ state1_red.
  ghash_block_t diff0, diff1;
  hardened_xor(ctx->state0.data, ctx_redundant.state0.data, kGhashBlockNumWords,
               diff0.data);
  hardened_xor(ctx->state1.data, ctx_redundant.state1.data, kGhashBlockNumWords,
               diff1.data);

  HARDENED_CHECK_EQ(
      consttime_memeq_byte(diff0.data, diff1.data, kGhashBlockNumBytes),
      kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

status_t ghash_handle_enc_initial_counter_block(
    const uint32_t *enc_initial_counter_block0,
    const uint32_t *enc_initial_counter_block1, ghash_context_t *ctx) {
  // correction_term0 = S0 * (H0 + 1).
  ghash_block_t s0 __attribute__((cleanup(ghash_block_shred)));
  hardened_memcpy(s0.data, enc_initial_counter_block0, kGhashBlockNumWords);
  block_reverse_bits_in_bytes(&s0);
  ghash_block_t mul_tmp __attribute__((cleanup(ghash_block_shred)));
  galois_mul_state_key(&s0, &ctx->hash_subkey0, &mul_tmp);
  block_xor(&mul_tmp, &s0, &ctx->correction_term0);

  // correction_term1 = S0 * H1.
  galois_mul_state_key(&s0, &ctx->hash_subkey1, &ctx->correction_term1);

  // correction_term1_init = S1 * H1.
  ghash_block_t s1 __attribute__((cleanup(ghash_block_shred)));
  hardened_memcpy(s1.data, enc_initial_counter_block1, kGhashBlockNumWords);
  block_reverse_bits_in_bytes(&s1);
  galois_mul_state_key(&s1, &ctx->hash_subkey1, &ctx->correction_term1_init);

  // Save the encrypted initial counter blocks into the ghash context as we
  // need them throughout the ghash computations.
  hardened_memcpy(ctx->enc_initial_counter_block0.data, s0.data,
                  kGhashBlockNumWords);
  hardened_memcpy(ctx->enc_initial_counter_block1.data, s1.data,
                  kGhashBlockNumWords);

  // Update the checksum.
  ctx->checksum = ghash_context_integrity_checksum(ctx);

  return LAUNDERED_OTCRYPTO_OK;
}

status_t ghash_final(ghash_context_t *ctx, uint32_t *result) {
  // Check that the context's checksum is correct.
  HARDENED_CHECK_EQ(ghash_context_integrity_checksum_check(ctx),
                    kHardenedBoolTrue);

  // Tag = (state0 + state1) + S1
  ghash_block_t tmp_block __attribute__((cleanup(ghash_block_shred)));
  ghash_block_t final_block __attribute__((cleanup(ghash_block_shred)));
  hardened_xor(ctx->state0.data, ctx->state1.data, kGhashBlockNumWords,
               tmp_block.data);
  hardened_xor(tmp_block.data, ctx->enc_initial_counter_block1.data,
               kGhashBlockNumWords, final_block.data);
  block_reverse_bits_in_bytes(&final_block);

  HARDENED_TRY(
      randomized_bytecopy(result, final_block.data, kGhashBlockNumBytes));

  return OTCRYPTO_OK;
}
