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

enum {
  /* Log2 of the number of bytes in an AES block. */
  kAesBlockLog2NumBytes = 4,
};
OT_ASSERT_ENUM_VALUE(kAesBlockNumBytes, 1 << kAesBlockLog2NumBytes);

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
 * Product table for a given hash subkey.
 *
 * See `make_product_table`.
 */
typedef struct aes_gcm_product_table {
  aes_block_t products[16];
} aes_gcm_product_table_t;

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
static inline void block_xor(const aes_block_t *x, const aes_block_t *y,
                             aes_block_t *out) {
  for (size_t i = 0; i < kAesBlockNumWords; ++i) {
    out->data[i] = x->data[i] ^ y->data[i];
  }
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
  /* TODO: replace with rev8 once bitmanip extension is enabled. */
  uint32_t out = 0;
  for (size_t i = 0; i < sizeof(uint32_t); ++i) {
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
  for (size_t i = 0; i < kAesBlockNumWords; ++i) {
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
 * Get the size of the last block for a given input size.
 *
 * Equivalent to `sz % kAesBlockNumBytes`, except that if `sz` is a multiple of
 * `kAesBlockNumBytes` then this will return `kAesBlockNumBytes` (since the
 * last block would then be a full block).
 *
 * Assumes that `sz` is nonzero.
 *
 * @param sz Number of bytes in the buffer, must be nonzero
 * @return Number of bytes in the last block
 */
static inline size_t get_last_block_num_bytes(size_t sz) {
  size_t remainder = sz % kAesBlockNumBytes;
  if (remainder == 0) {
    return kAesBlockNumBytes;
  }
  return remainder;
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
  if (get_last_block_num_bytes(sz) != kAesBlockNumBytes) {
    out += 1;
  }
  return out;
}

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
  return reverse_bytes(reverse_bytes(word) + 1);
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
 * @param[out] product_table Buffer for output
 */
static void make_product_table(const aes_block_t *H,
                               aes_gcm_product_table_t *tbl) {
  // Initialize 0 * H = 0.
  memset(tbl->products[0].data, 0, kAesBlockNumBytes);
  // Initialize 1 * H = H.
  memcpy(tbl->products[0x8].data, H->data, kAesBlockNumBytes);

  // To get remaining entries, we use a variant of "shift and add"; in
  // polynomial terms, a shift is a multiplication by x. Note that, because the
  // processor represents bytes with the MSB on the left and NIST uses a fully
  // little-endian polynomial representation with the MSB on the right, we have
  // to reverse the bits of the indices.
  for (size_t i = 2; i < 16; i += 2) {
    // Find the product corresponding to (i >> 1) * H and multiply by x to
    // shift 1; this will be i * H.
    galois_mulx(&tbl->products[reverse_bits(i >> 1)],
                &tbl->products[reverse_bits(i)]);

    // Add H to i * H to get (i + 1) * H.
    block_xor(&tbl->products[reverse_bits(i)], H,
              &tbl->products[reverse_bits(i + 1)]);
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
 * The `tbl` input should be a precomputed table with the products of H and
 * 256 all possible byte values (see `make_product_table`).
 *
 * This operation corresponds to multiplication in the Galois field with order
 * 2^128, modulo the polynomial x^128 +  x^8 + x^2 + x + 1
 *
 * @param p Polynomial to multiply
 * @param tbl Precomputed product table for the hash subkey
 * @param[out] result Block in which to store output
 */
static void galois_mul(const aes_block_t *p, const aes_gcm_product_table_t *tbl,
                       aes_block_t *result) {
  // Initialize the result to 0.
  memset(result->data, 0, kAesBlockNumBytes);

  // 4-bit windows, so number of windows is 2x number of bytes.
  const size_t kNumWindows = kAesBlockNumBytes << 1;

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
      uint8_t overflow = block_byte_get(result, kAesBlockNumBytes - 1) & 0x0f;
      // Shift `result` to the right, discarding high bits.
      block_shiftr(result, 4);
      // Look up the product of `overflow` and the low terms of the modulus in
      // the precomputed table.
      uint16_t reduce_term = kGFReduceTable[overflow];
      // Add (xor) this product to the low bits to complete modular reduction.
      // This works because (low + x^128 * high) is equivalent to (low + (x^128
      // - modulus) * high).
      result->data[0] ^= reduce_term;
    }

    // Add the product of the next window and H to `result`. We process the
    // windows starting with the most significant polynomial terms, which means
    // starting from the last byte and proceeding to the first.
    uint8_t pi = block_byte_get(p, (kNumWindows - 1 - i) >> 1);

    // Select the less significant 4 bits if i is even, or the more significant
    // 4 bits if i is odd. This does not need to be constant time, since the
    // values of i in this loop are constant.
    if ((i & 1) == 1) {
      pi >>= 4;
    } else {
      pi &= 0x0f;
    }
    block_xor(result, &tbl->products[pi], result);
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
 * @param tbl Precomputed product table
 * @param input_len Length of input in bytes
 * @param input Input buffer
 * @param state GHASH state, updated in place
 */
static void aes_gcm_ghash_update(const aes_gcm_product_table_t *tbl,
                                 const size_t input_len, const uint8_t *input,
                                 aes_block_t *state) {
  // Calculate the number of AES blocks needed for the input.
  size_t nblocks = get_nblocks(input_len);

  // Main loop.
  for (size_t i = 0; i < nblocks; ++i) {
    // Construct block i of the input.
    aes_block_t input_block;
    if (i == nblocks - 1) {
      // Last block may be partial; pad with zeroes.
      size_t nbytes = get_last_block_num_bytes(input_len);
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
    galois_mul(state, tbl, &yH);
    memcpy(state->data, yH.data, kAesBlockNumBytes);
  }
}

aes_error_t aes_gcm_ghash(const aes_block_t *hash_subkey,
                          const size_t input_len, const uint8_t *input,
                          aes_block_t *output) {
  // Compute the product table for H.
  aes_gcm_product_table_t tbl;
  make_product_table(hash_subkey, &tbl);

  // If the input length is not a multiple of the block size, fail.
  if (get_last_block_num_bytes(input_len) != kAesBlockNumBytes) {
    return kAesInternalError;
  }

  // Initialize the GHASH state to 0.
  memset(output->data, 0, kAesBlockNumBytes);

  // Update the GHASH state with the input.
  aes_gcm_ghash_update(&tbl, input_len, input, output);

  return kAesOk;
}

/**
 * One-shot version of the AES encryption API for a single block.
 */
static aes_error_t aes_encrypt_block(const aes_key_t key, const aes_block_t *iv,
                                     const aes_block_t *input,
                                     aes_block_t *output) {
  aes_error_t err = aes_encrypt_begin(key, iv);
  if (err != kAesOk) {
    return err;
  }
  err = aes_update(/*dest*/ NULL, input);
  if (err != kAesOk) {
    return err;
  }
  err = aes_update(output, /*src*/ NULL);
  if (err != kAesOk) {
    return err;
  }
  err = aes_end();
  if (err != kAesOk) {
    return err;
  }
  return kAesOk;
}

/**
 * Implements the GCTR function as specified in SP800-38D, section 6.5.
 *
 * The block cipher is fixed to AES. Note that the GCTR function is a modified
 * version of the AES-CTR mode of encryption.
 *
 * Input must be less than 2^32 blocks long; that is, `len` < 2^36, since each
 * block is 16 bytes.
 *
 * @param key The AES key
 * @param icb Initial counter block, 128 bits
 * @param len Number of bytes for input and output
 * @param input Pointer to input buffer (may be NULL if `len` is 0)
 * @param[out] output Pointer to output buffer (same size as input, may be the
 * same buffer)
 */
aes_error_t aes_gcm_gctr(const aes_key_t key, const aes_block_t *icb,
                         const size_t len, const uint8_t *input,
                         uint8_t *output) {
  // If the input is empty, the output must be as well. Since the output length
  // is 0, simply return.
  if (len == 0) {
    return kAesOk;
  }

  // NULL pointers are not allowed for nonzero input length.
  if (input == NULL || output == NULL) {
    return kAesInternalError;
  }

  // TODO: add support for sideloaded keys.
  if (key.sideload != kHardenedBoolFalse) {
    return kAesInternalError;
  }

  // Key must be intended for CTR mode.
  if (key.mode != kAesCipherModeCtr) {
    return kAesInternalError;
  }

  // Initial IV = ICB.
  aes_block_t iv;
  memcpy(iv.data, icb->data, kAesBlockNumBytes);

  // Calculate the number of blocks needed to represent the input. Since we
  // checked for empty input above, nblocks must be at least 1.
  size_t nblocks = get_nblocks(len);
  for (size_t i = 0; i < nblocks; ++i) {
    // Retrieve the next block of input. All blocks are full-size except for
    // the last block, which may be partial. If the block is partial, the input
    // data will be padded with zeroes.
    aes_block_t block_in;
    size_t nbytes = kAesBlockNumBytes;
    if (i == nblocks - 1) {
      // Last block is partial; copy the bytes that exist and set the rest of
      // the block to 0.
      nbytes = get_last_block_num_bytes(len);
      memset(block_in.data, 0, kAesBlockNumBytes);
      memcpy(block_in.data, &input[i * kAesBlockNumBytes], nbytes);
    } else {
      // This block is a full block.
      memcpy(block_in.data, &input[i * kAesBlockNumBytes], kAesBlockNumBytes);
    }

    // Run the AES-CTR encryption operation on the next block of input.
    aes_block_t block_out;
    aes_error_t err = aes_encrypt_block(key, &iv, &block_in, &block_out);
    if (err != kAesOk) {
      return err;
    }

    // Copy the result block into the output buffer, truncating some bytes if
    // the input block was partial.
    memcpy(&output[i * kAesBlockNumBytes], block_out.data, nbytes);

    // Update the counter block with inc32().
    block_inc32(&iv);
  }

  return kAesOk;
}

/**
 * Verify that the lengths of AES-GCM parameters are acceptable.
 *
 * This routine can be used for both authenticated encryption and authenticated
 * decryption; the lengths of the plaintext and ciphertext always match, and
 * `plaintext_len` may represent either.
 *
 * @param iv_len IV length in bytes
 * @param plaintext_len Plaintext/ciphertext length in bytes
 * @param aad_len Associated data length in bytes
 */
static hardened_bool_t check_buffer_lengths(const size_t iv_len,
                                            const size_t plaintext_len,
                                            const size_t aad_len) {
  // Check IV length (must be 96 or 128 bits = 12 or 16 bytes).
  if (iv_len != 12 && iv_len != 16) {
    return kHardenedBoolFalse;
  }

  // Check plaintext/AAD length. Both must be less than 2^32 bytes long. This
  // is stricter than NIST requires, but SP800-38D also allows implementations
  // to stipulate lower length limits.
  if (plaintext_len > UINT32_MAX || aad_len > UINT32_MAX) {
    return kHardenedBoolFalse;
  }

  return kHardenedBoolTrue;
}

/**
 * Compute the hash subkey for AES-GCM.
 *
 * This routine computes the hash subkey H and the product table for H; see
 * `make_product_table` for representation details.
 *
 * If any step in this process fails, the function returns an error and the
 * output should not be used.
 *
 * @param key AES key
 * @param[out] tbl Destination for the output hash subkey product table
 * @return OK or error
 */
static aes_error_t aes_gcm_hash_subkey(const aes_key_t key,
                                       aes_gcm_product_table_t *tbl) {
  // Compute the initial hash subkey H = AES_K(0). Note that to get this
  // result from AES_CTR, we set both the IV and plaintext to zero; this way,
  // AES-CTR's final XOR with the plaintext does nothing.
  aes_block_t zero;
  memset(zero.data, 0, kAesBlockNumBytes);
  aes_block_t hash_subkey;
  aes_error_t err = aes_encrypt_block(key, &zero, &zero, &hash_subkey);
  if (err != kAesOk) {
    return err;
  }

  // Compute the product table for H.
  make_product_table(&hash_subkey, tbl);

  return kAesOk;
}

/**
 * Compute the counter block based on the given IV and hash subkey.
 *
 * This block is called J0 in the NIST documentation, and is the same for both
 * encryption and decryption.
 *
 * @param iv_len IV length in bytes
 * @param iv IV value
 * @param tbl Product table for the hash subkey H
 * @param[out] j0 Destination for the output counter block
 * @return OK or error
 */
static aes_error_t aes_gcm_counter(const size_t iv_len, const uint8_t *iv,
                                   aes_gcm_product_table_t *tbl,
                                   aes_block_t *j0) {
  if (iv_len == 12) {
    // If the IV is 96 bits, then J0 = (IV || {0}^31 || 1).
    memcpy(j0->data, iv, iv_len);
    // Set the last word to 1 (as a big-endian integer).
    j0->data[kAesBlockNumWords - 1] = reverse_bytes(1);
  } else if (iv_len == 16) {
    // If the IV is 128 bits, then J0 = GHASH(H, IV || {0}^120 || 0x80), where
    // {0}^120 means 120 zero bits (15 0x00 bytes).
    memset(j0->data, 0, kAesBlockNumBytes);
    aes_gcm_ghash_update(tbl, iv_len, iv, j0);
    uint8_t buffer[kAesBlockNumBytes];
    memset(buffer, 0, kAesBlockNumBytes);
    buffer[kAesBlockNumBytes - 1] = 0x80;
    aes_gcm_ghash_update(tbl, kAesBlockNumBytes, buffer, j0);
  } else {
    // Should not happen; invalid IV length.
    return kAesInternalError;
  }

  return kAesOk;
}

/**
 * Compute the AES-GCM authentication tag.
 *
 * @param key AES key
 * @param tbl Product table for the hash subkey H
 * @param ciphertext_len Length of the ciphertext in bytes
 * @param ciphertext Ciphertext value
 * @param aad_len Length of the associated data in bytes
 * @param aad Associated data value
 * @param j0 Counter block (J0 in the NIST specification)
 * @param[out] tag Buffer for output tag (128 bits)
 */
static aes_error_t aes_gcm_compute_tag(const aes_key_t key,
                                       const aes_gcm_product_table_t *tbl,
                                       const size_t ciphertext_len,
                                       const uint8_t *ciphertext,
                                       const size_t aad_len, const uint8_t *aad,
                                       const aes_block_t *j0, uint8_t *tag) {
  // Compute S = GHASH(H, expand(A) || expand(C) || len64(A) || len64(C))
  // where:
  //   * A is the aad, C is the ciphertext
  //   * expand(x) pads x to a multiple of 128 bits by adding zeroes to the
  //     right-hand side
  //   * len64(x) is the length of x in bits expressed as a
  //     big-endian 64-bit integer.

  // Compute GHASH(H, expand(A) || expand(C)).
  aes_block_t s;
  memset(s.data, 0, kAesBlockNumBytes);
  aes_gcm_ghash_update(tbl, aad_len, aad, &s);
  aes_gcm_ghash_update(tbl, ciphertext_len, ciphertext, &s);

  // Compute len64(A) and len64(C) by computing the length in *bits* (shift by
  // 3) and then converting to big-endian.
  uint64_t last_block[2] = {
      __builtin_bswap64(((uint64_t)aad_len) * 8),
      __builtin_bswap64(((uint64_t)ciphertext_len) * 8),
  };

  // Use memcpy() to avoid violating strict aliasing when converting to bytes.
  uint8_t last_block_bytes[sizeof(last_block)];
  memcpy(last_block_bytes, last_block, sizeof(last_block));

  // Finish computing S by appending (len64(A) || len64(C)).
  aes_gcm_ghash_update(tbl, kAesBlockNumBytes, last_block_bytes, &s);

  // Compute the tag T = GCTR(K, J0, S).
  uint8_t s_data_bytes[sizeof(s.data)];
  memcpy(s_data_bytes, s.data, sizeof(s.data));
  return aes_gcm_gctr(key, j0, kAesBlockNumBytes, s_data_bytes, tag);
}

aes_error_t aes_gcm_encrypt(const aes_key_t key, const size_t iv_len,
                            const uint8_t *iv, const size_t plaintext_len,
                            const uint8_t *plaintext, const size_t aad_len,
                            const uint8_t *aad, uint8_t *ciphertext,
                            uint8_t *tag) {
  // Check that the input parameter sizes are valid.
  if (check_buffer_lengths(iv_len, plaintext_len, aad_len) !=
      kHardenedBoolTrue) {
    return kAesInternalError;
  }

  // Compute the hash subkey H as a product table.
  aes_gcm_product_table_t Htbl;
  aes_error_t err = aes_gcm_hash_subkey(key, &Htbl);
  if (err != kAesOk) {
    return err;
  }

  // Compute the counter block (called J0 in the NIST specification).
  aes_block_t j0;
  err = aes_gcm_counter(iv_len, iv, &Htbl, &j0);
  if (err != kAesOk) {
    return err;
  }

  // Compute inc32(J0).
  aes_block_t j0_inc;
  memcpy(j0_inc.data, j0.data, kAesBlockNumBytes);
  block_inc32(&j0_inc);

  // Compute ciphertext C = GCTR(K, inc32(J0), plaintext).
  err = aes_gcm_gctr(key, &j0_inc, plaintext_len, plaintext, ciphertext);
  if (err != kAesOk) {
    return err;
  }

  // Compute the authentication tag T.
  return aes_gcm_compute_tag(key, &Htbl, plaintext_len, ciphertext, aad_len,
                             aad, &j0, tag);
}

aes_error_t aes_gcm_decrypt(const aes_key_t key, const size_t iv_len,
                            const uint8_t *iv, const size_t ciphertext_len,
                            const uint8_t *ciphertext, const size_t aad_len,
                            const uint8_t *aad, const uint8_t *tag,
                            uint8_t *plaintext, hardened_bool_t *success) {
  // Check that the input parameter sizes are valid.
  if (check_buffer_lengths(iv_len, ciphertext_len, aad_len) !=
      kHardenedBoolTrue) {
    return kAesInternalError;
  }

  // Compute the hash subkey H as a product table.
  aes_gcm_product_table_t Htbl;
  aes_error_t err = aes_gcm_hash_subkey(key, &Htbl);
  if (err != kAesOk) {
    return err;
  }

  // Compute the counter block (called J0 in the NIST specification).
  aes_block_t j0;
  err = aes_gcm_counter(iv_len, iv, &Htbl, &j0);
  if (err != kAesOk) {
    return err;
  }

  // Compute the expected authentication tag T.
  uint8_t expected_tag[kAesGcmTagNumBytes];
  err = aes_gcm_compute_tag(key, &Htbl, ciphertext_len, ciphertext, aad_len,
                            aad, &j0, expected_tag);
  if (err != kAesOk) {
    return err;
  }

  // Copy expected and actual tag to word-size buffers to avoid violating
  // strict aliasing rules.
  uint32_t expected_tag_words[kAesGcmTagNumWords];
  uint32_t tag_words[kAesGcmTagNumWords];
  memcpy(expected_tag_words, expected_tag, kAesGcmTagNumBytes);
  memcpy(tag_words, tag, kAesGcmTagNumBytes);

  // Compare the expected tag to the actual tag (in constant time).
  *success = hardened_memeq(expected_tag_words, tag_words, kAesGcmTagNumWords);
  if (*success != kHardenedBoolTrue) {
    // If authentication fails, do not proceed to decryption; simply exit
    // with success = False. We still use `kAesOk` because there was no
    // internal error during the authentication check.
    return kAesOk;
  }

  // Compute plaintext P = GCTR(K, inc32(J0), ciphertext).
  block_inc32(&j0);
  return aes_gcm_gctr(key, &j0, ciphertext_len, ciphertext, plaintext);
}
