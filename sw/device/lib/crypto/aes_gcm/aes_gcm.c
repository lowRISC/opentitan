// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"

enum {
  /* Log2 of the number of bytes in an AES block. */
  kAesBlockLog2NumBytes = 4,
};
OT_ASSERT_ENUM_VALUE(kAesBlockNumBytes, 1 << kAesBlockLog2NumBytes);

/**
 * Precomputed modular reduction constants for Galois field multiplication.
 *
 * The entry with index i in this table is equal to i * 0xe1, where the bytes i
 * and 0xe1 are interpreted as polynomials in the GCM Galois field. For
 * example, 0xe1 = 11100001 is the degree-8 polynomial x^8 + x^2 + x + 1.
 *
 * The field modulus is 2^128 + x^8 + x^2 + x + 1. Therefore, if a field
 * element is shifted, it can be reduced by multiplying the high bits (128 and
 * above) by 0xe1 and adding them to the low bits.
 *
 * Using these tables provides about a 2.2x speedup over using the naive method
 * described in the FIPS document for a 2-block plaintext and 2-block aad. This
 * method also defers much more work to preprocessing rather than per-block
 * computation in GHASH, so the longer the plaintext and aad, the bigger the
 * speedup will be.
 */
static const uint16_t kGFReduceTable[256] = {
    0x0000, 0xc201, 0x8403, 0x4602, 0x0807, 0xca06, 0x8c04, 0x4e05, 0x100e,
    0xd20f, 0x940d, 0x560c, 0x1809, 0xda08, 0x9c0a, 0x5e0b, 0x201c, 0xe21d,
    0xa41f, 0x661e, 0x281b, 0xea1a, 0xac18, 0x6e19, 0x3012, 0xf213, 0xb411,
    0x7610, 0x3815, 0xfa14, 0xbc16, 0x7e17, 0x4038, 0x8239, 0xc43b, 0x063a,
    0x483f, 0x8a3e, 0xcc3c, 0x0e3d, 0x5036, 0x9237, 0xd435, 0x1634, 0x5831,
    0x9a30, 0xdc32, 0x1e33, 0x6024, 0xa225, 0xe427, 0x2626, 0x6823, 0xaa22,
    0xec20, 0x2e21, 0x702a, 0xb22b, 0xf429, 0x3628, 0x782d, 0xba2c, 0xfc2e,
    0x3e2f, 0x8070, 0x4271, 0x0473, 0xc672, 0x8877, 0x4a76, 0x0c74, 0xce75,
    0x907e, 0x527f, 0x147d, 0xd67c, 0x9879, 0x5a78, 0x1c7a, 0xde7b, 0xa06c,
    0x626d, 0x246f, 0xe66e, 0xa86b, 0x6a6a, 0x2c68, 0xee69, 0xb062, 0x7263,
    0x3461, 0xf660, 0xb865, 0x7a64, 0x3c66, 0xfe67, 0xc048, 0x0249, 0x444b,
    0x864a, 0xc84f, 0x0a4e, 0x4c4c, 0x8e4d, 0xd046, 0x1247, 0x5445, 0x9644,
    0xd841, 0x1a40, 0x5c42, 0x9e43, 0xe054, 0x2255, 0x6457, 0xa656, 0xe853,
    0x2a52, 0x6c50, 0xae51, 0xf05a, 0x325b, 0x7459, 0xb658, 0xf85d, 0x3a5c,
    0x7c5e, 0xbe5f, 0x00e1, 0xc2e0, 0x84e2, 0x46e3, 0x08e6, 0xcae7, 0x8ce5,
    0x4ee4, 0x10ef, 0xd2ee, 0x94ec, 0x56ed, 0x18e8, 0xdae9, 0x9ceb, 0x5eea,
    0x20fd, 0xe2fc, 0xa4fe, 0x66ff, 0x28fa, 0xeafb, 0xacf9, 0x6ef8, 0x30f3,
    0xf2f2, 0xb4f0, 0x76f1, 0x38f4, 0xfaf5, 0xbcf7, 0x7ef6, 0x40d9, 0x82d8,
    0xc4da, 0x06db, 0x48de, 0x8adf, 0xccdd, 0x0edc, 0x50d7, 0x92d6, 0xd4d4,
    0x16d5, 0x58d0, 0x9ad1, 0xdcd3, 0x1ed2, 0x60c5, 0xa2c4, 0xe4c6, 0x26c7,
    0x68c2, 0xaac3, 0xecc1, 0x2ec0, 0x70cb, 0xb2ca, 0xf4c8, 0x36c9, 0x78cc,
    0xbacd, 0xfccf, 0x3ece, 0x8091, 0x4290, 0x0492, 0xc693, 0x8896, 0x4a97,
    0x0c95, 0xce94, 0x909f, 0x529e, 0x149c, 0xd69d, 0x9898, 0x5a99, 0x1c9b,
    0xde9a, 0xa08d, 0x628c, 0x248e, 0xe68f, 0xa88a, 0x6a8b, 0x2c89, 0xee88,
    0xb083, 0x7282, 0x3480, 0xf681, 0xb884, 0x7a85, 0x3c87, 0xfe86, 0xc0a9,
    0x02a8, 0x44aa, 0x86ab, 0xc8ae, 0x0aaf, 0x4cad, 0x8eac, 0xd0a7, 0x12a6,
    0x54a4, 0x96a5, 0xd8a0, 0x1aa1, 0x5ca3, 0x9ea2, 0xe0b5, 0x22b4, 0x64b6,
    0xa6b7, 0xe8b2, 0x2ab3, 0x6cb1, 0xaeb0, 0xf0bb, 0x32ba, 0x74b8, 0xb6b9,
    0xf8bc, 0x3abd, 0x7cbf, 0xbebe};

/**
 * Performs a bitwise XOR of two blocks.
 *
 * This operation corresponds to addition in the Galois field.
 *
 * @param condition Either 0 or 1
 * @param x First operand block
 * @param y Second operand block
 * @param out Buffer in which to store output; can be the same as one or both
 * operands.
 */
static inline void block_xor(const aes_block_t *x, const aes_block_t *y,
                             aes_block_t *out) {
  for (size_t i = 0; i < kAesBlockNumWords; i++) {
    out->data[i] = x->data[i] ^ y->data[i];
  }
}

/**
 * Reverse the bits of a byte.
 *
 * @param word Input word.
 * @return Word with bytes reversed.
 */
static uint8_t reverse_bits(uint8_t byte) {
  uint8_t out = 0;
  for (size_t i = 0; i < 8; i++) {
    out <<= 1;
    out |= (byte >> i) & 1;
  }
  return out;
}

/**
 * Reverse the bytes of a 32-bit word.
 *
 * This function is convenient for converting between the processor's native
 * integers, which are little-endian, and NIST's integer representation, which
 * is big-endian.
 *
 * @param word Input word.
 * @return Word with bytes reversed.
 */
static uint32_t reverse_bytes(uint32_t word) {
  uint32_t out = 0;
  for (size_t i = 0; i < sizeof(uint32_t); i++) {
    out <<= 8;
    out |= (word >> (i << 3)) & 255;
  }
  return out;
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
static inline void block_shiftr(aes_block_t *block, size_t nbits) {
  // To perform a "right shift" with respect to the big-endian block
  // representation, we traverse the words of the block and, for each word,
  // reverse the bytes, save the new LSB as `carry`, shift right, set the MSB
  // to the last block's carry, and then reverse the bytes back.
  uint32_t carry = 0;
  for (size_t i = 0; i < kAesBlockNumWords; i++) {
    uint32_t rev = reverse_bytes(block->data[i]);
    uint32_t next_carry = rev & ((1 << nbits) - 1);
    rev >>= nbits;
    rev |= carry << (32 - nbits);
    carry = next_carry;
    block->data[i] = reverse_bytes(rev);
  }
}

/**
 * Retrieve the byte at a given index from the AES block.
 *
 * @param block Input AES block
 * @param index Index of byte to retrieve (must be < `kAesBlockNumBytes`)
 * @return Value of block[index]
 */
static inline uint8_t block_byte_get(const aes_block_t *block, size_t index) {
  return (uint8_t)((char *)block->data)[index];
}

/**
 * Get the number of bytes past the last full block of the buffer.
 *
 * Equivalent to `sz % kAesBlockNumBytes`. Assumes that `kAesBlockNumBytes` is
 * a power of 2.
 *
 * @param sz Number of bytes to represent
 * @return Offset of end of buffer from last full block
 */
static inline size_t get_block_offset(size_t sz) {
  return sz & (kAesBlockNumBytes - 1);
}

/**
 * Get the minimum number of AES blocks needed to represent `sz` bytes.
 *
 * This routine does not run in constant time and should not be used for
 * sensitive input values.
 *
 * @param sz Number of bytes to represent
 * @return Minimum number of blocks needed
 */
static inline size_t get_nblocks(size_t sz) {
  size_t out = sz >> kAesBlockLog2NumBytes;
  if (get_block_offset(sz) != 0) {
    out += 1;
  }
  return out;
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
 * @param out Buffer for output
 */
static inline void galois_mulx(const aes_block_t *p, aes_block_t *out) {
  // Get the very rightmost bit of the input block (coefficient of x^127).
  uint8_t p127 = block_byte_get(p, kAesBlockNumBytes - 1) & 1;
  // Set the output to p >> 1.
  memcpy(out->data, p->data, kAesBlockNumBytes);
  block_shiftr(out, 1);
  // If the highest coefficient was 1, then subtract the polynomial that
  // corresponds to (modulus - 2^128).
  uint32_t mask = 0 - p127;
  out->data[0] ^= (0xe1 & mask);
}

/**
 * Construct a product table for the hash subkey H.
 *
 * The product table entry at index i is equal to i * H, where both i and H are
 * interpreted as Galois field polynomials.
 *
 * @param H Hash subkey
 * @param product_table Buffer for output
 */
static void make_product_table(const aes_block_t *H,
                               aes_block_t product_table[256]) {
  // Initialize 0 * H = 0.
  memset(product_table[0].data, 0, kAesBlockNumBytes);
  // Initialize 1 * H = H.
  memcpy(product_table[0x80].data, H->data, kAesBlockNumBytes);

  // To get remaining entries, we use a variant of "shift and add"; in
  // polynomial terms, a shift is a multiplication by x. Note that, because the
  // processor represents bytes with the MSB on the left and NIST uses a fully
  // little-endian polynomial representation with the MSB on the right, we have
  // to reverse the bits of the indices.
  for (size_t i = 2; i < 256; i += 2) {
    // Find the product corresponding to (i >> 1) * H and multiply by x to
    // shift 1; this will be i * H.
    galois_mulx(&product_table[reverse_bits(i >> 1)],
                &product_table[reverse_bits(i)]);

    // Add H to i * H to get (i + 1) * H.
    block_xor(&product_table[reverse_bits(i)], H,
              &product_table[reverse_bits(i + 1)]);
  }
}

/**
 * Computes the "product block" as defined in NIST SP800-38D, section 6.3.
 *
 * The NIST documentation shows a very slow double-and-add algorithm, which
 * iterates through the first operand bit-by-bit. However, since the second
 * operand is always the hash subkey H, we can speed things up significantly
 * with a little precomputation.
 *
 * The `H_table` input should be a precomputed table with the products of H and
 * 256 all possible byte values (see `make_product_table`).
 *
 * This operation corresponds to multiplication in the Galois field with order
 * 2^128, modulo the polynomial x^128 +  x^8 + x^2 + x + 1
 *
 * @param p Polynomial to multiply
 * @param H_table Precomputed product table for the hash subkey
 * @param result Block in which to store output
 */
static void galois_mul(const aes_block_t *p, const aes_block_t H_table[256],
                       aes_block_t *result) {
  // Initialize the result to 0.
  memset(result->data, 0, kAesBlockNumBytes);

  // To compute the product, we iterate through the bytes of the input block,
  // considering the most significant (in polynomial terms) first. For each
  // byte b, we:
  //   * multiply `result` by x^8 (shift all coefficients to the right)
  //   * reduce the shifted `result` modulo the field modulus
  //   * look up the product `b * H` and add it to `result`
  //
  // We can skip the shift and reduce steps on the first iteration, since
  // `result` is 0.
  for (size_t i = 0; i < kAesBlockNumBytes; i++) {
    if (i != 0) {
      // Save the most significant byte of `result` before shifting.
      uint8_t overflow = block_byte_get(result, kAesBlockNumBytes - 1);
      // Shift `result` to the right, discarding high bits.
      block_shiftr(result, 8);
      // Look up the product of `overflow` and the low terms of the modulus in
      // the precomputed table.
      uint16_t reduce_term = kGFReduceTable[overflow];
      // Add (xor) this product to the low bits to complete modular reduction.
      // This works because (low + x^128 * high) is equivalent to (low + (x^128
      // - modulus) * high).
      result->data[0] ^= reduce_term;
    }

    // Add the product of the next byte and H to `result`. We process the bytes
    // starting with the most significant polynomial terms, which means
    // starting from the last byte and proceeding to the first.
    uint8_t pi = block_byte_get(p, kAesBlockNumBytes - 1 - i);
    block_xor(result, &H_table[pi], result);
  }
}

/**
 * Advances the GHASH state for the given input.
 *
 * This function is convenient for computing the GHASH of large, concatenated
 * buffers. Given a state representing GHASH(A) and a new input B, this
 * function will return a state representing GHASH(A || B || <padding for B>).
 *
 * Pads the input with 0s on the right-hand side if needed so that the input
 * size is a multiple of the block size.
 *
 * The product table should match the format from `make_product_table`.
 *
 * @param H_table Precomputed product table
 * @param input_len Length of input in bytes
 * @param input Input buffer
 * @param state GHASH state, updated in place
 */
static void aes_gcm_ghash_update(const aes_block_t H_table[256],
                                 const size_t input_len, const uint8_t *input,
                                 aes_block_t *state) {
  // Calculate the number of AES blocks needed for the input.
  size_t nblocks = get_nblocks(input_len);

  // Main loop.
  for (size_t i = 0; i < nblocks; i++) {
    // Construct block i of the input.
    aes_block_t input_block;
    if ((i == nblocks - 1) && (get_block_offset(input_len) != 0)) {
      // Last block is not full; pad with zeroes.
      size_t nbytes = get_block_offset(input_len);
      memset(input_block.data, 0, kAesBlockNumBytes);
      memcpy(input_block.data, input, nbytes);
    } else {
      // Full block; copy data and advance input pointer.
      memcpy(input_block.data, input, kAesBlockNumBytes);
      input += kAesBlockNumBytes;
    }
    // XOR `state` with the next input block.
    block_xor(state, &input_block, state);
    // Multiply state by H and update.
    aes_block_t yH;
    galois_mul(state, H_table, &yH);
    memcpy(state->data, yH.data, kAesBlockNumBytes);
  }
}

aes_error_t aes_gcm_ghash(const aes_block_t *hash_subkey,
                          const size_t input_len, const uint8_t *input,
                          aes_block_t *output) {
  // Compute the product table for H.
  aes_block_t H_table[256];
  make_product_table(hash_subkey, H_table);

  // If the input length is not a multiple of the block size, fail.
  if (get_block_offset(input_len) != 0) {
    return kAesInternalError;
  }

  // Calculate the number of AES blocks needed for the input.
  size_t nblocks = get_nblocks(input_len);

  // Initialize the GHASH state to 0.
  memset(output->data, 0, kAesBlockNumBytes);

  // Update the GHASH state with the input.
  aes_gcm_ghash_update(H_table, input_len, input, output);

  return kAesOk;
}
