// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_padding.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/include/hash.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'p', 'a')

/**
 * Digest identifiers for different hash functions (little-endian).
 *
 * See Note 1 in RFC 8017.
 */
static const uint8_t kSha256DigestIdentifier[] = {
    0x20, 0x04, 0x00, 0x05, 0x01, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x31, 0x30,
};
static const uint8_t kSha384DigestIdentifier[] = {
    0x30, 0x04, 0x00, 0x05, 0x02, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x41, 0x30,
};
static const uint8_t kSha512DigestIdentifier[] = {
    0x40, 0x04, 0x00, 0x05, 0x03, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x51, 0x30,
};

/**
 * Get the length of the DER encoding for the given hash function's digests.
 *
 * See RFC 8017, Appendix B.1. The encoding consists of the digest algorithm
 * identifier and then the digest itself.
 *
 * @param hash_mode Hash function to use.
 * @param[out] len Byte-length of the DER encoding of the digest.
 * @param OTCRYPTO_BAD_ARGS if the hash function is not valid, otherwise OK.
 */
OT_WARN_UNUSED_RESULT
static status_t digest_info_length_get(const hash_mode_t hash_mode,
                                       size_t *len) {
  switch (hash_mode) {
    case kHashModeSha256:
      *len = sizeof(kSha256DigestIdentifier) + kSha256DigestBytes;
      return OTCRYPTO_OK;
    case kHashModeSha384:
      *len = sizeof(kSha384DigestIdentifier) + kSha384DigestBytes;
      return OTCRYPTO_OK;
    case kHashModeSha512:
      *len = sizeof(kSha512DigestIdentifier) + kSha512DigestBytes;
      return OTCRYPTO_OK;
    default:
      // Unsupported or unrecognized hash function.
      return OTCRYPTO_BAD_ARGS;
  };

  // Unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Get the DER encoding for the hash function's digests.
 *
 * See RFC 8017, Appendix B.1.
 *
 * The caller must ensure that enough space is allocated for the encoding; use
 * `digest_info_length()` to check before calling this function. Only certain
 * hash functions are supported.
 *
 * Writes the encoding in little-endian, which is reversed compared to the RFC.
 *
 * @param message_digest Message digest to encode.
 * @param[out] encoding DER encoding of the digest.
 * @return OTCRYPTO_BAD_ARGS if the hash function is not valid, otherwise OK.
 */
OT_WARN_UNUSED_RESULT
static status_t digest_info_write(const hash_digest_t *message_digest,
                                  uint32_t *encoding) {
  switch (message_digest->mode) {
    case kHashModeSha256:
      if (message_digest->len != kSha256DigestWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      memcpy(encoding + kSha256DigestWords, &kSha256DigestIdentifier,
             sizeof(kSha256DigestIdentifier));
      break;
    case kHashModeSha384:
      if (message_digest->len != kSha384DigestWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      memcpy(encoding + kSha384DigestWords, &kSha384DigestIdentifier,
             sizeof(kSha384DigestIdentifier));
      break;
    case kHashModeSha512:
      if (message_digest->len != kSha512DigestWords) {
        return OTCRYPTO_BAD_ARGS;
      }
      memcpy(encoding + kSha512DigestWords, &kSha512DigestIdentifier,
             sizeof(kSha512DigestIdentifier));
      break;
    default:
      // Unsupported or unrecognized hash function.
      return OTCRYPTO_BAD_ARGS;
  };

  // Copy the digest into the encoding, reversing the order of bytes.
  for (size_t i = 0; i < message_digest->len / 2; i++) {
    uint32_t tmp = __builtin_bswap32(message_digest->data[i]);
    encoding[i] =
        __builtin_bswap32(message_digest->data[message_digest->len - 1 - i]);
    encoding[message_digest->len - 1 - i] = tmp;
  }

  return OTCRYPTO_OK;
}

status_t rsa_padding_pkcs1v15_encode(const hash_digest_t *message_digest,
                                     size_t encoded_message_len,
                                     uint32_t *encoded_message) {
  // Initialize all bits of the encoded message to 1.
  size_t encoded_message_bytelen = encoded_message_len * sizeof(uint32_t);
  memset(encoded_message, 0xff, encoded_message_bytelen);

  // Get a byte-sized pointer to the encoded message data.
  unsigned char *buf = (unsigned char *)encoded_message;

  // Set the last byte to 0x00 and the second-to-last byte to 0x01.
  buf[encoded_message_bytelen - 1] = 0x00;
  buf[encoded_message_bytelen - 2] = 0x01;

  // Get the length of the digest info (called T in the RFC).
  size_t tlen;
  HARDENED_TRY(digest_info_length_get(message_digest->mode, &tlen));

  if (tlen + 3 + 8 >= encoded_message_bytelen) {
    // Invalid encoded message length/hash function combination; the RFC
    // specifies that the 0xff padding must be at least 8 octets.
    return OTCRYPTO_BAD_ARGS;
  }

  // Write the digest info to the start of the buffer.
  HARDENED_TRY(digest_info_write(message_digest, encoded_message));

  // Set one byte to 0 just after the digest info.
  buf[tlen] = 0x00;

  return OTCRYPTO_OK;
}

status_t rsa_padding_pkcs1v15_verify(const hash_digest_t *message_digest,
                                     const uint32_t *encoded_message,
                                     const size_t encoded_message_len,
                                     hardened_bool_t *result) {
  // Re-encode the message.
  uint32_t expected_encoded_message[encoded_message_len];
  HARDENED_TRY(rsa_padding_pkcs1v15_encode(message_digest, encoded_message_len,
                                           expected_encoded_message));

  // Compare with the expected value.
  *result = hardened_memeq(encoded_message, expected_encoded_message,
                           ARRAYSIZE(expected_encoded_message));
  return OTCRYPTO_OK;
}

/**
 * Get the output size in words for the given hash function.
 *
 * Returns an error if the hash mode is unsupported, unrecognized, or does not
 * have a fixed length.
 *
 * @param hash_mode Hash function.
 * @param[out] num_words Output length in 32-bit words.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
static status_t digest_wordlen_get(hash_mode_t hash_mode, size_t *num_words) {
  *num_words = 0;
  switch (hash_mode) {
    case kHashModeSha3_224:
      *num_words = 224 / 32;
      break;
    case kHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_256:
      *num_words = 256 / 32;
      break;
    case kHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_384:
      *num_words = 384 / 32;
      break;
    case kHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_512:
      *num_words = 512 / 32;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(num_words, 0);

  return OTCRYPTO_OK;
}

/**
 * Mask generation function MGF1 (RFC 8017, appendix B.2.1).
 *
 * The `mask` parameter is 32-bit aligned because this makes it more secure and
 * efficient to operate and compare with the mask. However, the mask length is
 * not necessarily a multiple of the word size. This routine guarantees that
 * any extra bytes at the end of the mask will be initialized, but does not
 * make any guarantees about their values.
 *
 * @param hash_mode Hash function to use.
 * @param seed Seed data.
 * @param seed_len Length of seed data in bytes.
 * @param mask_len Intended byte-length of the mask.
 * @param[out] mask Destination buffer for mask.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
static status_t mgf1(hash_mode_t hash_mode, const uint8_t *seed,
                     size_t seed_len, size_t mask_len, uint32_t *mask) {
  // Check that the number of iterations won't overflow the counter.
  size_t digest_wordlen;
  HARDENED_TRY(digest_wordlen_get(hash_mode, &digest_wordlen));
  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);
  size_t num_iterations = ceil_div(mask_len, digest_bytelen);
  if (num_iterations > UINT32_MAX) {
    return OTCRYPTO_BAD_ARGS;
  }

  // First, process the iterations in which the entire digest will fit in the
  // `mask` buffer.
  uint8_t hash_input[seed_len + sizeof(uint32_t)];
  memcpy(hash_input, seed, seed_len);
  for (uint32_t i = 0; i < num_iterations - 1; i++) {
    uint32_t ctr = __builtin_bswap32(i);
    memcpy(hash_input + seed_len, &ctr, sizeof(uint32_t));
    hash_digest_t digest = {
        .data = mask, .len = digest_wordlen, .mode = hash_mode};
    HARDENED_TRY(otcrypto_hash(
        (crypto_const_byte_buf_t){
            .data = hash_input,
            .len = sizeof(hash_input),
        },
        &digest));
    mask += digest_wordlen;
    mask_len -= digest_bytelen;
  }
  HARDENED_CHECK_LE(mask_len, digest_bytelen);

  // Last iteration is special; use an intermediate buffer in case the digest
  // is longer than the remaining mask buffer.
  uint32_t ctr = __builtin_bswap32(num_iterations - 1);
  memcpy(hash_input + seed_len, &ctr, sizeof(uint32_t));
  uint32_t digest_data[digest_wordlen];
  hash_digest_t digest = {
      .data = digest_data, .len = digest_wordlen, .mode = hash_mode};
  HARDENED_TRY(otcrypto_hash(
      (crypto_const_byte_buf_t){.data = hash_input, .len = sizeof(hash_input)},
      &digest));
  hardened_memcpy(mask, digest_data, ceil_div(mask_len, sizeof(uint32_t)));
  return OTCRYPTO_OK;
}

/**
 * Reverse the byte-order of a word array in-place.
 *
 * @param input_len Length of input in 32-bit words.
 * @param[in,out] input Input array, modified in-place.
 */
static inline void reverse_bytes(size_t input_len, uint32_t *input) {
  for (size_t i = 0; i < (input_len + 1) / 2; i++) {
    size_t j = input_len - 1 - i;
    uint32_t tmp = input[j];
    input[j] = __builtin_bswap32(input[i]);
    input[i] = __builtin_bswap32(tmp);
  }
}

/**
 * Helper function to construct the "H" value for PSS encoding.
 *
 * As described in RFC 8017, H = Hash(0x0000000000000000 || digest || salt).
 * This value needs to be computed for both encryption and decryption. The hash
 * function should match the hash function from the message digest, so the
 * caller is responsible for ensuring that there is enough space in `h` to hold
 * another digest of the same type.
 *
 * @param message_digest Message digest to encode.
 * @param salt Salt value.
 * @param salt_len Length of the salt in 32-bit words.
 * @param[out] h Resulting digest, H.
 */
OT_WARN_UNUSED_RESULT
static status_t pss_construct_h(const hash_digest_t *message_digest,
                                const uint32_t *salt, size_t salt_len,
                                uint32_t *h) {
  // Create a buffer for M' = (0x0000000000000000 || digest || salt).
  size_t m_prime_wordlen = 2 + message_digest->len + salt_len;
  uint32_t m_prime[m_prime_wordlen];
  m_prime[0] = 0;
  m_prime[1] = 0;
  uint32_t *digest_dst = &m_prime[2];
  uint32_t *salt_dst = digest_dst + message_digest->len;
  hardened_memcpy(digest_dst, message_digest->data, message_digest->len);
  if (salt_len > 0) {
    hardened_memcpy(salt_dst, salt, salt_len);
  }

  // Construct H = Hash(M').
  hash_digest_t h_buffer = {
      .data = h, .len = message_digest->len, .mode = message_digest->mode};
  return otcrypto_hash(
      (crypto_const_byte_buf_t){.data = (unsigned char *)m_prime,
                                .len = sizeof(m_prime)},
      &h_buffer);
}

status_t rsa_padding_pss_encode(const hash_digest_t *message_digest,
                                const uint32_t *salt, size_t salt_len,
                                size_t encoded_message_len,
                                uint32_t *encoded_message) {
  // Check that the message length is long enough.
  size_t digest_bytelen = message_digest->len * sizeof(uint32_t);
  size_t salt_bytelen = salt_len * sizeof(uint32_t);
  size_t encoded_message_bytelen = encoded_message_len * sizeof(uint32_t);
  if (encoded_message_bytelen < salt_bytelen + digest_bytelen + 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct H = Hash(0x0000000000000000 || digest || salt).
  uint32_t h[message_digest->len];
  HARDENED_TRY(pss_construct_h(message_digest, salt, salt_len, h));

  // Construct DB = 00...00 || 0x01 || salt.
  size_t db_bytelen = encoded_message_bytelen - digest_bytelen - 1;
  uint32_t db[ceil_div(db_bytelen, sizeof(uint32_t))];
  memset(db, 0, sizeof(db));
  unsigned char *db_bytes = (unsigned char *)db;
  db_bytes[db_bytelen - 1 - salt_bytelen] = 0x01;
  if (salt_bytelen > 0) {
    memcpy(db_bytes + (db_bytelen - salt_bytelen), salt, salt_bytelen);
  }

  // Compute the mask.
  uint32_t mask[ARRAYSIZE(db)];
  HARDENED_TRY(mgf1(message_digest->mode, (unsigned char *)h, sizeof(h),
                    db_bytelen, mask));

  // Compute maskedDB = DB ^ mask.
  for (size_t i = 0; i < ARRAYSIZE(db); i++) {
    db[i] ^= mask[i];
  }

  // Set the most significant bit of the first byte of maskedDB to 0. This
  // ensures the encoded message is less than the modulus. Corresponds to RFC
  // 8017, section 9.1.1, step 11 (where emBits is modLen - 1).
  db_bytes[0] &= 0x7f;

  // Compute the final encoded message and reverse the byte-order.
  //   EM = maskedDB || H || 0xbc
  unsigned char *encoded_message_bytes = (unsigned char *)encoded_message;
  hardened_memcpy(encoded_message, db, ARRAYSIZE(db));
  memcpy(encoded_message_bytes + db_bytelen, h, sizeof(h));
  encoded_message_bytes[encoded_message_bytelen - 1] = 0xbc;
  reverse_bytes(encoded_message_len, encoded_message);
  return OTCRYPTO_OK;
}

status_t rsa_padding_pss_verify(const hash_digest_t *message_digest,
                                uint32_t *encoded_message,
                                size_t encoded_message_len,
                                hardened_bool_t *result) {
  // Initialize the result to false.
  *result = kHardenedBoolFalse;

  // Check that the message length is long enough.
  size_t digest_bytelen = message_digest->len * sizeof(uint32_t);
  size_t salt_bytelen = digest_bytelen;
  size_t encoded_message_bytelen = encoded_message_len * sizeof(uint32_t);
  if (encoded_message_bytelen < salt_bytelen + digest_bytelen + 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Reverse the byte-order.
  reverse_bytes(encoded_message_len, encoded_message);

  // Check the last byte.
  unsigned char *encoded_message_bytes = (unsigned char *)encoded_message;
  if (encoded_message_bytes[encoded_message_bytelen - 1] != 0xbc) {
    *result = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Extract the masked "DB" value. Zero the last bytes if needed.
  size_t db_bytelen = encoded_message_bytelen - digest_bytelen - 1;
  uint32_t db[ceil_div(db_bytelen, sizeof(uint32_t))];
  memcpy(db, encoded_message_bytes, db_bytelen);
  if (sizeof(db) > db_bytelen) {
    memset(((unsigned char *)db) + db_bytelen, 0, sizeof(db) - db_bytelen);
  }

  // Extract H.
  uint32_t h[message_digest->len];
  memcpy(h, encoded_message_bytes + db_bytelen, sizeof(h));

  // Compute the mask = MFG(H, emLen - hLen - 1). Zero the last bytes if
  // needed.
  uint32_t mask[ARRAYSIZE(db)];
  HARDENED_TRY(mgf1(message_digest->mode, (unsigned char *)h, sizeof(h),
                    db_bytelen, mask));
  if (sizeof(mask) > db_bytelen) {
    memset(((unsigned char *)mask) + db_bytelen, 0, sizeof(mask) - db_bytelen);
  }

  // Unmask the "DB" value.
  for (size_t i = 0; i < ARRAYSIZE(db); i++) {
    db[i] ^= mask[i];
  }

  // Set the most significant bit of the first byte of maskedDB to 0.
  // Corresponds to RFC 8017, section 9.1.2 step 9 (emBits is modLen - 1).
  unsigned char *db_bytes = (unsigned char *)db;
  db_bytes[0] &= 0x7f;

  // Check that DB starts with all zeroes followed by a single 1 byte. Copy in
  // enough trailing bytes to fill the last word, so that we can use
  // `hardened_memeq` here.
  size_t padding_bytelen = db_bytelen - salt_bytelen;
  uint32_t exp_padding[ceil_div(padding_bytelen, sizeof(uint32_t))];
  unsigned char *exp_padding_bytes = (unsigned char *)exp_padding;
  memset(exp_padding, 0, padding_bytelen - 1);
  exp_padding_bytes[padding_bytelen - 1] = 0x01;
  memcpy(exp_padding_bytes + padding_bytelen, db_bytes + padding_bytelen,
         sizeof(exp_padding) - padding_bytelen);
  hardened_bool_t padding_eq =
      hardened_memeq(db, exp_padding, ARRAYSIZE(exp_padding));
  if (padding_eq != kHardenedBoolTrue) {
    *result = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Extract the salt.
  uint32_t salt[message_digest->len];
  memcpy(salt, db_bytes + db_bytelen - salt_bytelen, sizeof(salt));

  // Construct the expected value of H and compare.
  uint32_t exp_h[message_digest->len];
  HARDENED_TRY(pss_construct_h(message_digest, salt, ARRAYSIZE(salt), exp_h));
  *result = hardened_memeq(h, exp_h, ARRAYSIZE(exp_h));
  return OTCRYPTO_OK;
}
