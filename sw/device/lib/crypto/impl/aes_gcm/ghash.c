// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('g', 'h', 'a')

enum {
  /**
   * Log2 of the number of bytes in an AES block.
   */
  kGhashBlockLog2NumBytes = 4,
  /**
   * Number of windows for Galois field pre-computed tables.
   *
   * We suse 4-bit windows, so the number of windows is 2x the number of bytes
   * in a block.
   */
  kNumWindows = kGhashBlockNumBytes << 1,
};
static_assert(kGhashBlockNumBytes == (1 << kGhashBlockLog2NumBytes),
              "kGhashBlockLog2NumBytes does not match kGhashBlockNumBytes");

/**
 * Precomputed modular reduction constants for Galois field multiplication.
 *
 * This implementation uses 4-bit windows. The bytes here represent 12-bit
 * little-endian values.
 *
 * The entry with index i in this table is equal to i * 0xe1, where the bytes i
 * and 0xe1 are interpreted as polynomials in the GCM Galois field. For
 * example, 0xe1 = 0b1110_0001 is the degree-8 polynomial x^8 + x^2 + x + 1.
 *
 * The field modulus for GCM is 2^128 + x^8 + x^2 + x + 1. Therefore, if a
 * field element is shifted, it can be reduced by multiplying the high bits
 * (128 and above) by 0xe1 and adding them to the low bits.
 *
 * There is a size/speed tradeoff in window size. For 8-bit windows, GHASH
 * becomes significantly faster, but the overhead for computing the product
 * table of a given hash subkey becomes higher, so larger windows are slower
 * for smaller inputs but faster for large inputs.
 */
static const uint16_t kGFReduceTable[16] = {
    0x0000, 0x201c, 0x4038, 0x6024, 0x8070, 0xa06c, 0xc048, 0xe054,
    0x00e1, 0x20fd, 0x40d9, 0x60c5, 0x8091, 0xa08d, 0xc0a9, 0xe0b5};

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
 * Logical right shift of an AES block.
 *
 * NIST represents AES blocks as big-endian, and a "right shift" in that
 * representation means shifting out the LSB. However, the processor is
 * little-endian, so we need to reverse the bytes before shifting.
 *
 * @param block Input AES block, modified in-place
 * @param nbits Number of bits to shift
 */
static inline void block_shiftr(ghash_block_t *block, size_t nbits) {
  // To perform a "right shift" with respect to the big-endian block
  // representation, we traverse the words of the block and, for each word,
  // reverse the bytes, save the new LSB as `carry`, shift right, set the MSB
  // to the last block's carry, and then reverse the bytes back.
  uint32_t carry = 0;
  for (size_t i = 0; i < kGhashBlockNumWords; ++i) {
    uint32_t rev = __builtin_bswap32(block->data[i]);
    uint32_t next_carry = rev & ((1 << nbits) - 1);
    rev >>= nbits;
    rev |= carry << (32 - nbits);
    carry = next_carry;
    block->data[i] = __builtin_bswap32(rev);
  }
}

/**
 * Retrieve the byte at a given index from the block.
 *
 * @param block Input cipher block
 * @param index Index of byte to retrieve (must be < `kGhashBlockNumBytes`)
 * @return Value of block[index]
 */
static inline uint8_t block_byte_get(const ghash_block_t *block, size_t index) {
  return ((char *)block->data)[index];
}

/**
 * Multiply an element of the GCM Galois field by the polynomial `x`.
 *
 * This corresponds to a shift right in the bit representation, and then
 * reduction with the field modulus.
 *
 * Runs in constant time.
 *
 * @param p Polynomial to be multiplied
 * @param[out] out Buffer for output
 */
static inline void galois_mulx(const ghash_block_t *p, ghash_block_t *out) {
  // Get the very rightmost bit of the input block (coefficient of x^127).
  uint8_t p127 = block_byte_get(p, kGhashBlockNumBytes - 1) & 1;
  // Set the output to p >> 1.
  randomized_bytecopy(out->data, p->data, kGhashBlockNumBytes);
  block_shiftr(out, 1);
  // If the highest coefficient was 1, then subtract the polynomial that
  // corresponds to (modulus - 2^128).
  uint32_t mask = 0 - p127;
  out->data[0] ^= (0xe1 & mask);
}

/**
 * Reverse the bits of a 4-bit number.
 *
 * @param byte Input byte.
 * @return byte with lower 4 bits reversed and upper 4 unmodified.
 */
static uint8_t reverse_bits(uint8_t byte) {
  /* TODO: replace with rev.n (from 0.93 draft of bitmanip) once bitmanip
   * extension is enabled. */
  uint8_t out = 0;
  for (size_t i = 0; i < 4; ++i) {
    out <<= 1;
    out |= (byte >> i) & 1;
  }
  return out;
}

uint32_t ghash_context_integrity_checksum(const ghash_context_t *ghash_ctx) {
  uint32_t ctx;
  crc32_init(&ctx);
  // Compute the checksum only over a single share to avoid side-channel
  // leakage. From a FI perspective only covering one key share is fine as
  // (a) manipulating the second share with FI has only limited use to an
  // adversary and (b) when manipulating the entire pointer to the key structure
  // the checksum check fails.
  crc32_add(&ctx, (unsigned char *)ghash_ctx->tbl0, sizeof(ghash_ctx->tbl0));
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

status_t ghash_init_subkey(const uint32_t *hash_subkey, ghash_block_t *tbl) {
  // Initialize 0 * H = 0.
  memset(tbl[0].data, 0, kGhashBlockNumBytes);
  // Initialize 1 * H = H.
  HARDENED_TRY(
      randomized_bytecopy(tbl[0x8].data, hash_subkey, kGhashBlockNumBytes));

  // To get remaining entries, we use a variant of "shift and add"; in
  // polynomial terms, a shift is a multiplication by x. Note that, because the
  // processor represents bytes with the MSB on the left and NIST uses a fully
  // little-endian polynomial representation with the MSB on the right, we have
  // to reverse the bits of the indices.
  for (uint8_t i = 2; i < 16; i += 2) {
    // Find the product corresponding to (i >> 1) * H and multiply by x to
    // shift 1; this will be i * H.
    galois_mulx(&tbl[reverse_bits(i >> 1)], &tbl[reverse_bits(i)]);

    // Add H to i * H to get (i + 1) * H.
    block_xor(&tbl[reverse_bits(i)], &tbl[0x8], &tbl[reverse_bits(i + 1)]);
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

  return OTCRYPTO_OK;
}

/**
 * Multiply the GHASH state by the hash subkey.
 *
 * See NIST SP800-38D, section 6.3.
 *
 * The NIST documentation shows a very slow double-and-add algorithm, which
 * iterates through the first operand bit-by-bit. However, since the second
 * operand is always the hash subkey H, we can speed things up significantly
 * with precomputed tables.
 *
 * This operation corresponds to multiplication in the Galois field with order
 * 2^128, modulo the polynomial x^128 +  x^8 + x^2 + x + 1
 *
 * @param state GHASH state.
 * @param tbl Product table for the masked hash subkey.
 * @return Multiplication of the state and the hash subkey.
 */
static ghash_block_t galois_mul_state_key(ghash_block_t state,
                                          ghash_block_t tbl[16]) {
  // Initialize the multiplication result to 0.
  ghash_block_t result;
  memset(result.data, 0, kGhashBlockNumBytes);

  // To compute the product, we iterate through the bytes of the input block,
  // considering the most significant (in polynomial terms) first. For each
  // byte b, we:
  //   * multiply `result` by x^8 (shift all coefficients to the right)
  //   * reduce the shifted `result` modulo the field modulus
  //   * look up the product `b * H` and add it to `result`
  //
  // We can skip the shift and reduce steps on the first iteration, since
  // `result` is 0.
  for (size_t i = 0; i < kNumWindows; ++i) {
    if (i != 0) {
      // Save the most significant half-byte of `result` before shifting.
      uint8_t overflow =
          block_byte_get(&result, kGhashBlockNumBytes - 1) & 0x0f;
      // Shift `result` to the right, discarding high bits.
      block_shiftr(&result, 4);
      // Look up the product of `overflow` and the low terms of the modulus in
      // the precomputed table.
      uint16_t reduce_term = kGFReduceTable[overflow];
      // Add (xor) this product to the low bits to complete modular reduction.
      // This works because (low + x^128 * high) is equivalent to (low + (x^128
      // - modulus) * high).
      result.data[0] ^= reduce_term;
    }

    // Add the product of the next window and H to `result`. We process the
    // windows starting with the most significant polynomial terms, which means
    // starting from the last byte and proceeding to the first.
    uint8_t tbl_index = block_byte_get(&state, (kNumWindows - 1 - i) >> 1);

    // Select the less significant 4 bits if i is even, or the more significant
    // 4 bits if i is odd. This does not need to be constant time, since the
    // values of i in this loop are constant.
    if ((i & 1) == 1) {
      tbl_index >>= 4;
    } else {
      tbl_index &= 0x0f;
    }
    block_xor(&result, &tbl[tbl_index], &result);
  }
  return result;
}

/**
 * Single-block update function for GHASH.
 *
 * @param ctx GHASH context.
 * @param block Block to incorporate.
 */
static status_t ghash_process_block(ghash_context_t *ctx,
                                    ghash_block_t *block) {
  ghash_block_t s0_tmp;
  ghash_block_t s1_tmp;

  if (ctx->ghash_block_cnt == 0) {
    // Process share 0.
    // share0_tmp = (S0 + T0) * H0
    hardened_memcpy(s0_tmp.data, block->data, kGhashBlockNumWords);
    hardened_xor_in_place(s0_tmp.data, ctx->enc_initial_counter_block0.data,
                          kGhashBlockNumWords);
    s0_tmp = galois_mul_state_key(s0_tmp, ctx->tbl0);

    // Apply the correction terms for state share 0.
    // share0 = share0_tmp + (S0*(H0+1))
    hardened_memcpy(ctx->state0.data, s0_tmp.data, kGhashBlockNumWords);
    hardened_xor_in_place(ctx->state0.data, ctx->correction_term0.data,
                          kGhashBlockNumWords);

    // Clear the RF before operating on the second share to avoid leakage
    // between both shares.
    ibex_clear_rf();

    // Process share 1.
    // share1_tmp = (S1 + T0) * H1
    hardened_memcpy(s1_tmp.data, block->data, kGhashBlockNumWords);
    hardened_xor_in_place(s1_tmp.data, ctx->enc_initial_counter_block1.data,
                          kGhashBlockNumWords);
    ibex_clear_rf();
    s1_tmp = galois_mul_state_key(s1_tmp, ctx->tbl1);

    // Apply the correction terms for state share 1.
    // share1 = share1_tmp + correction_term1
    hardened_memcpy(ctx->state1.data, s1_tmp.data, kGhashBlockNumWords);
    hardened_xor_in_place(ctx->state1.data, ctx->correction_term1_init.data,
                          kGhashBlockNumWords);
  } else {
    // Process share 0.
    // tmp = (share0+TN-1)+share1
    ghash_block_t tmp;
    hardened_memcpy(tmp.data, block->data, kGhashBlockNumWords);
    hardened_xor_in_place(tmp.data, ctx->state0.data, kGhashBlockNumWords);
    hardened_xor_in_place(tmp.data, ctx->state1.data, kGhashBlockNumWords);

    // s0_tmp = tmp * H0
    s0_tmp = galois_mul_state_key(tmp, ctx->tbl0);

    // Apply the correction terms for state share 0.
    // share0 = share0_tmp + (S0*(H0+1))
    hardened_memcpy(ctx->state0.data, s0_tmp.data, kGhashBlockNumWords);
    hardened_xor_in_place(ctx->state0.data, ctx->correction_term0.data,
                          kGhashBlockNumWords);

    // Process share 1.
    // share1_tmp = tmp * H1
    s1_tmp = galois_mul_state_key(tmp, ctx->tbl1);

    // Apply the correction terms for state share 1.
    // share1 = share1_tmp + (S0*H0)
    hardened_memcpy(ctx->state1.data, s1_tmp.data, kGhashBlockNumWords);
    hardened_xor_in_place(ctx->state1.data, ctx->correction_term1.data,
                          kGhashBlockNumWords);
  }

  // Check that the context's checksum is correct.
  HARDENED_CHECK_EQ(ghash_context_integrity_checksum_check(ctx),
                    kHardenedBoolTrue);

  // Increment the number of processed ghash block counter.
  ctx->ghash_block_cnt++;

  return OTCRYPTO_OK;
}

status_t ghash_process_full_blocks(ghash_context_t *ctx, size_t partial_len,
                                   ghash_block_t *partial, size_t input_len,
                                   const uint8_t *input) {
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
    HARDENED_TRY(ghash_process_block(ctx, partial));

    // Process any remaining full blocks of input.
    while (input_len >= kGhashBlockNumBytes) {
      randomized_bytecopy(partial->data, input, kGhashBlockNumBytes);
      HARDENED_TRY(ghash_process_block(ctx, partial));
      input += kGhashBlockNumBytes;
      input_len -= kGhashBlockNumBytes;
    }

    // Copy any remaining input into the partial block.
    randomized_bytecopy(partial->data, input, input_len);
  }

  return OTCRYPTO_OK;
}

status_t ghash_update(ghash_context_t *ctx, size_t input_len,
                      const uint8_t *input) {
  // Process all full blocks and write the remaining non-full data into
  // `partial`.
  ghash_block_t partial = {.data = {0}};
  HARDENED_TRY(ghash_process_full_blocks(ctx, 0, &partial, input_len, input));

  // Check if there is data remaining, and process it if so.
  size_t partial_len = input_len % kGhashBlockNumBytes;
  if (partial_len != 0) {
    unsigned char *partial_bytes = (unsigned char *)partial.data;
    memset(partial_bytes + partial_len, 0, kGhashBlockNumBytes - partial_len);
    HARDENED_TRY(ghash_process_block(ctx, &partial));
  }

  return OTCRYPTO_OK;
}

status_t ghash_update_redundant(ghash_context_t *ctx, size_t input_len,
                                const uint8_t *input) {
  // Copy ctx.
  ghash_context_t ctx_redundant;
  randomized_bytecopy(&ctx_redundant, ctx, sizeof(ctx_redundant));

  HARDENED_TRY(ghash_update(ctx, input_len, input));

  ghash_update(&ctx_redundant, input_len, input);

  // Compare the GHASH state. Do this only at a single share to avoid
  // introducing SCA leakage. Use consttime_memeq_byte() to avoid DFA.
  HARDENED_CHECK_EQ(
      consttime_memeq_byte(&ctx->state0.data, ctx_redundant.state0.data,
                           kGhashBlockNumBytes),
      kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

status_t ghash_handle_enc_initial_counter_block(
    const uint32_t *enc_initial_counter_block0,
    const uint32_t *enc_initial_counter_block1, ghash_context_t *ctx) {
  // correction_term0 = S0 * (H0 + 1).
  ghash_block_t s0;
  hardened_memcpy(s0.data, enc_initial_counter_block0, kGhashBlockNumWords);
  ghash_block_t mul_tmp = galois_mul_state_key(s0, ctx->tbl0);
  block_xor(&mul_tmp, &s0, &ctx->correction_term0);

  // correction_term1 = S0 * H1.
  ctx->correction_term1 = galois_mul_state_key(s0, ctx->tbl1);

  // correction_term1_init = S1 * H1.
  ghash_block_t s1;
  hardened_memcpy(s1.data, enc_initial_counter_block1, kGhashBlockNumWords);
  ctx->correction_term1_init = galois_mul_state_key(s1, ctx->tbl1);

  // Save the encrypted initial counter blocks into the ghash context as we
  // need them throughout the ghash computations.
  hardened_memcpy(ctx->enc_initial_counter_block0.data,
                  enc_initial_counter_block0, kGhashBlockNumWords);
  hardened_memcpy(ctx->enc_initial_counter_block1.data,
                  enc_initial_counter_block1, kGhashBlockNumWords);

  // Update the checksum.
  ctx->checksum = ghash_context_integrity_checksum(ctx);

  return OTCRYPTO_OK;
}

status_t ghash_final(ghash_context_t *ctx, uint32_t *result) {
  // Check that the context's checksum is correct.
  HARDENED_CHECK_EQ(ghash_context_integrity_checksum_check(ctx),
                    kHardenedBoolTrue);

  // Tag = (state0 + state1) + S1
  ghash_block_t tmp_block;
  ghash_block_t final_block;
  hardened_xor(ctx->state0.data, ctx->state1.data, kGhashBlockNumWords,
               tmp_block.data);
  hardened_xor(tmp_block.data, ctx->enc_initial_counter_block1.data,
               kGhashBlockNumWords, final_block.data);

  HARDENED_TRY(
      randomized_bytecopy(result, final_block.data, kGhashBlockNumBytes));

  return OTCRYPTO_OK;
}
