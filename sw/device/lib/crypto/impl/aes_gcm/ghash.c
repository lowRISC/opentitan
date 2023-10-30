// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"

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
  memcpy(out->data, p->data, kGhashBlockNumBytes);
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

void ghash_init_subkey(const uint32_t *hash_subkey, ghash_context_t *ctx) {
  // Initialize 0 * H = 0.
  memset(ctx->tbl[0].data, 0, kGhashBlockNumBytes);
  // Initialize 1 * H = H.
  memcpy(ctx->tbl[0x8].data, hash_subkey, kGhashBlockNumBytes);

  // To get remaining entries, we use a variant of "shift and add"; in
  // polynomial terms, a shift is a multiplication by x. Note that, because the
  // processor represents bytes with the MSB on the left and NIST uses a fully
  // little-endian polynomial representation with the MSB on the right, we have
  // to reverse the bits of the indices.
  for (uint8_t i = 2; i < 16; i += 2) {
    // Find the product corresponding to (i >> 1) * H and multiply by x to
    // shift 1; this will be i * H.
    galois_mulx(&ctx->tbl[reverse_bits(i >> 1)], &ctx->tbl[reverse_bits(i)]);

    // Add H to i * H to get (i + 1) * H.
    block_xor(&ctx->tbl[reverse_bits(i)], &ctx->tbl[0x8],
              &ctx->tbl[reverse_bits(i + 1)]);
  }
}

void ghash_init(ghash_context_t *ctx) {
  memset(ctx->state.data, 0, kGhashBlockNumBytes);
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
 * @param ctx GHASH context, updated in place.
 */
static void galois_mul_state_key(ghash_context_t *ctx) {
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
    uint8_t tbl_index = block_byte_get(&ctx->state, (kNumWindows - 1 - i) >> 1);

    // Select the less significant 4 bits if i is even, or the more significant
    // 4 bits if i is odd. This does not need to be constant time, since the
    // values of i in this loop are constant.
    if ((i & 1) == 1) {
      tbl_index >>= 4;
    } else {
      tbl_index &= 0x0f;
    }
    block_xor(&result, &ctx->tbl[tbl_index], &result);
  }

  memcpy(ctx->state.data, result.data, kGhashBlockNumBytes);
}

/**
 * Single-block update function for GHASH.
 *
 * @param ctx GHASH context.
 * @param block Block to incorporate.
 */
static void ghash_process_block(ghash_context_t *ctx, ghash_block_t *block) {
  // XOR `state` with the next input block.
  block_xor(&ctx->state, block, &ctx->state);
  // Multiply state by H in-place.
  galois_mul_state_key(ctx);
}

void ghash_process_full_blocks(ghash_context_t *ctx, size_t partial_len,
                               ghash_block_t *partial, size_t input_len,
                               const uint8_t *input) {
  if (input_len < kGhashBlockNumBytes - partial_len) {
    // Not enough data for a full block; copy into the partial block.
    unsigned char *partial_bytes = (unsigned char *)partial->data;
    memcpy(partial_bytes + partial_len, input, input_len);
  } else {
    // Construct a block from the partial data and the start of the new data.
    unsigned char *partial_bytes = (unsigned char *)partial->data;
    memcpy(partial_bytes + partial_len, input,
           kGhashBlockNumBytes - partial_len);
    input += kGhashBlockNumBytes - partial_len;
    input_len -= kGhashBlockNumBytes - partial_len;

    // Process the block.
    ghash_process_block(ctx, partial);

    // Process any remaining full blocks of input.
    while (input_len >= kGhashBlockNumBytes) {
      memcpy(partial->data, input, kGhashBlockNumBytes);
      ghash_process_block(ctx, partial);
      input += kGhashBlockNumBytes;
      input_len -= kGhashBlockNumBytes;
    }

    // Copy any remaining input into the partial block.
    memcpy(partial->data, input, input_len);
  }
}

void ghash_update(ghash_context_t *ctx, size_t input_len,
                  const uint8_t *input) {
  // Process all full blocks and write the remaining non-full data into
  // `partial`.
  ghash_block_t partial = {.data = {0}};
  ghash_process_full_blocks(ctx, 0, &partial, input_len, input);

  // Check if there is data remaining, and process it if so.
  size_t partial_len = input_len % kGhashBlockNumBytes;
  if (partial_len != 0) {
    unsigned char *partial_bytes = (unsigned char *)partial.data;
    memset(partial_bytes + partial_len, 0, kGhashBlockNumBytes - partial_len);
    ghash_process_block(ctx, &partial);
  }
}

void ghash_final(ghash_context_t *ctx, uint32_t *result) {
  memcpy(result, ctx->state.data, kGhashBlockNumBytes);
}
