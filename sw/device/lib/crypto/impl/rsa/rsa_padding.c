// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_padding.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/kmac.h"

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
/*
 * SHA-3 digest identifiers adapted from the SHA-2 identifers based on the
 * algorithm identifiers on
 * https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
 */
static const uint8_t kSha3_224DigestIdentifier[] = {
    0x1c, 0x04, 0x00, 0x05, 0x07, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x2d, 0x30,
};
static const uint8_t kSha3_256DigestIdentifier[] = {
    0x20, 0x04, 0x00, 0x05, 0x08, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x31, 0x30,
};
static const uint8_t kSha3_384DigestIdentifier[] = {
    0x30, 0x04, 0x00, 0x05, 0x09, 0x02, 0x04, 0x03, 0x65, 0x01,
    0x48, 0x86, 0x60, 0x09, 0x06, 0x0d, 0x30, 0x41, 0x30,
};
static const uint8_t kSha3_512DigestIdentifier[] = {
    0x40, 0x04, 0x00, 0x05, 0x0a, 0x02, 0x04, 0x03, 0x65, 0x01,
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
static status_t digest_info_length_get(const otcrypto_hash_mode_t hash_mode,
                                       size_t *len) {
  switch (hash_mode) {
    case kOtcryptoHashModeSha256:
      *len = sizeof(kSha256DigestIdentifier) + kHmacSha256DigestBytes;
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha384:
      *len = sizeof(kSha384DigestIdentifier) + kHmacSha384DigestBytes;
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha512:
      *len = sizeof(kSha512DigestIdentifier) + kHmacSha512DigestBytes;
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_224:
      *len = sizeof(kSha3_224DigestIdentifier) + kKmacSha3224DigestBytes;
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_256:
      *len = sizeof(kSha3_256DigestIdentifier) + kKmacSha3256DigestBytes;
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_384:
      *len = sizeof(kSha3_384DigestIdentifier) + kKmacSha3384DigestBytes;
      return OTCRYPTO_OK;
    case kOtcryptoHashModeSha3_512:
      *len = sizeof(kSha512DigestIdentifier) + kKmacSha3512DigestBytes;
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
static status_t digest_info_write(const otcrypto_hash_digest_t message_digest,
                                  uint32_t *encoding) {
  size_t digest_wordlen = 0;
  switch (message_digest.mode) {
    case kOtcryptoHashModeSha256:
      digest_wordlen = kHmacSha256DigestWords;
      memcpy(encoding + digest_wordlen, &kSha256DigestIdentifier,
             sizeof(kSha256DigestIdentifier));
      break;
    case kOtcryptoHashModeSha384:
      digest_wordlen = kHmacSha384DigestWords;
      memcpy(encoding + digest_wordlen, &kSha384DigestIdentifier,
             sizeof(kSha384DigestIdentifier));
      break;
    case kOtcryptoHashModeSha512:
      digest_wordlen = kHmacSha512DigestWords;
      memcpy(encoding + digest_wordlen, &kSha512DigestIdentifier,
             sizeof(kSha512DigestIdentifier));
      break;
    case kOtcryptoHashModeSha3_224:
      digest_wordlen = kKmacSha3224DigestWords;
      memcpy(encoding + digest_wordlen, &kSha3_224DigestIdentifier,
             sizeof(kSha3_224DigestIdentifier));
      break;
    case kOtcryptoHashModeSha3_256:
      digest_wordlen = kKmacSha3256DigestWords;
      memcpy(encoding + digest_wordlen, &kSha3_256DigestIdentifier,
             sizeof(kSha3_256DigestIdentifier));
      break;
    case kOtcryptoHashModeSha3_384:
      digest_wordlen = kKmacSha3384DigestWords;
      memcpy(encoding + digest_wordlen, &kSha3_384DigestIdentifier,
             sizeof(kSha3_384DigestIdentifier));
      break;
    case kOtcryptoHashModeSha3_512:
      digest_wordlen = kKmacSha3512DigestWords;
      memcpy(encoding + digest_wordlen, &kSha3_512DigestIdentifier,
             sizeof(kSha3_512DigestIdentifier));
      break;
    default:
      // Unsupported or unrecognized hash function.
      return OTCRYPTO_BAD_ARGS;
  };
  if (launder32(message_digest.len) != digest_wordlen) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(message_digest.len, digest_wordlen);

  // Copy the digest into the encoding, reversing the order of bytes.
  for (size_t i = 0; i < ceil_div(message_digest.len, 2); i++) {
    encoding[i] =
        __builtin_bswap32(message_digest.data[message_digest.len - 1 - i]);
    encoding[message_digest.len - 1 - i] =
        __builtin_bswap32(message_digest.data[i]);
  }

  return OTCRYPTO_OK;
}

status_t rsa_padding_pkcs1v15_encode(
    const otcrypto_hash_digest_t message_digest, size_t encoded_message_len,
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
  HARDENED_TRY(digest_info_length_get(message_digest.mode, &tlen));

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

status_t rsa_padding_pkcs1v15_verify(
    const otcrypto_hash_digest_t message_digest,
    const uint32_t *encoded_message, const size_t encoded_message_len,
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
static status_t digest_wordlen_get(otcrypto_hash_mode_t hash_mode,
                                   size_t *num_words) {
  *num_words = 0;
  switch (hash_mode) {
    case kOtcryptoHashModeSha3_224:
      *num_words = 224 / 32;
      break;
    case kOtcryptoHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoHashModeSha3_256:
      *num_words = 256 / 32;
      break;
    case kOtcryptoHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoHashModeSha3_384:
      *num_words = 384 / 32;
      break;
    case kOtcryptoHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoHashModeSha3_512:
      *num_words = 512 / 32;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(num_words, 0);

  return OTCRYPTO_OK;
}

/**
 * Run an iteration of a hash function using the HMAC or KMAC driver.
 *
 * Only supports fixed-length hash functions (SHA2 or SHA3), not XOFs.
 *
 * It is the caller's responsibility to ensure there is enough space allocated
 * at `digest` to hold the result.
 *
 * @param hash_mode Hash function to use.
 * @param message Message data to hash.
 * @param message_len Length of message data in bytes.
 * @param[out] digest Destination buffer.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t hash(otcrypto_hash_mode_t hash_mode, const uint8_t *message,
                     size_t message_len, uint32_t *digest) {
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha256);
      return hmac_hash_sha256(message, message_len, digest);
    case kOtcryptoHashModeSha384:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha384);
      return hmac_hash_sha384(message, message_len, digest);
    case kOtcryptoHashModeSha512:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha512);
      return hmac_hash_sha512(message, message_len, digest);
    case kOtcryptoHashModeSha3_224:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha3_224);
      return kmac_sha3_224(message, message_len, digest);
    case kOtcryptoHashModeSha3_256:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha3_256);
      return kmac_sha3_256(message, message_len, digest);
    case kOtcryptoHashModeSha3_384:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha3_384);
      return kmac_sha3_384(message, message_len, digest);
    case kOtcryptoHashModeSha3_512:
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha3_512);
      return kmac_sha3_512(message, message_len, digest);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
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
static status_t mgf1(otcrypto_hash_mode_t hash_mode, const uint8_t *seed,
                     size_t seed_len, size_t mask_len, uint32_t *mask) {
  size_t digest_wordlen;
  HARDENED_TRY(digest_wordlen_get(hash_mode, &digest_wordlen));
  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);

  uint8_t hash_input[seed_len + sizeof(uint32_t)];
  memcpy(hash_input, seed, seed_len);
  uint32_t i = 0;
  while (0 < mask_len) {
    uint32_t ctr = __builtin_bswap32(i);
    memcpy(hash_input + seed_len, &ctr, sizeof(uint32_t));
    if (mask_len < digest_bytelen) {
      // Digest won't fit in mask (last iteration). Use a temporary buffer.
      uint32_t digest[digest_wordlen];
      HARDENED_TRY(hash(hash_mode, hash_input, sizeof(hash_input), digest));
      hardened_memcpy(mask, digest, ceil_div(mask_len, sizeof(uint32_t)));
      mask_len = 0;
    } else {
      HARDENED_TRY(hash(hash_mode, hash_input, sizeof(hash_input), mask));
      mask_len -= digest_bytelen;
    }
    mask += digest_wordlen;
    i++;
  }
  HARDENED_CHECK_EQ(mask_len, 0);

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
static status_t pss_construct_h(const otcrypto_hash_digest_t message_digest,
                                const uint32_t *salt, size_t salt_len,
                                uint32_t *h) {
  // Create a buffer for M' = (0x0000000000000000 || digest || salt).
  size_t m_prime_wordlen = 2 + message_digest.len + salt_len;
  uint32_t m_prime[m_prime_wordlen];
  m_prime[0] = 0;
  m_prime[1] = 0;
  uint32_t *digest_dst = &m_prime[2];
  uint32_t *salt_dst = digest_dst + message_digest.len;
  hardened_memcpy(digest_dst, message_digest.data, message_digest.len);
  if (salt_len > 0) {
    hardened_memcpy(salt_dst, salt, salt_len);
  }

  // Construct H = Hash(M').
  return hash(message_digest.mode, (unsigned char *)m_prime, sizeof(m_prime),
              h);
}

status_t rsa_padding_pss_encode(const otcrypto_hash_digest_t message_digest,
                                const uint32_t *salt, size_t salt_len,
                                size_t encoded_message_len,
                                uint32_t *encoded_message) {
  // Check that the message length is long enough.
  size_t digest_bytelen = message_digest.len * sizeof(uint32_t);
  size_t salt_bytelen = salt_len * sizeof(uint32_t);
  size_t encoded_message_bytelen = encoded_message_len * sizeof(uint32_t);
  if (encoded_message_bytelen < salt_bytelen + digest_bytelen + 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct H = Hash(0x0000000000000000 || digest || salt).
  uint32_t h[message_digest.len];
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
  HARDENED_TRY(mgf1(message_digest.mode, (unsigned char *)h, sizeof(h),
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

status_t rsa_padding_pss_verify(const otcrypto_hash_digest_t message_digest,
                                uint32_t *encoded_message,
                                size_t encoded_message_len,
                                hardened_bool_t *result) {
  // Initialize the result to false.
  *result = kHardenedBoolFalse;

  // Check that the message length is long enough.
  size_t digest_bytelen = message_digest.len * sizeof(uint32_t);
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
  uint32_t h[message_digest.len];
  memcpy(h, encoded_message_bytes + db_bytelen, sizeof(h));

  // Compute the mask = MFG(H, emLen - hLen - 1). Zero the last bytes if
  // needed.
  uint32_t mask[ARRAYSIZE(db)];
  HARDENED_TRY(mgf1(message_digest.mode, (unsigned char *)h, sizeof(h),
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
  uint32_t salt[message_digest.len];
  memcpy(salt, db_bytes + db_bytelen - salt_bytelen, sizeof(salt));

  // Construct the expected value of H and compare.
  uint32_t exp_h[message_digest.len];
  HARDENED_TRY(pss_construct_h(message_digest, salt, ARRAYSIZE(salt), exp_h));
  *result = hardened_memeq(h, exp_h, ARRAYSIZE(exp_h));
  return OTCRYPTO_OK;
}

status_t rsa_padding_oaep_max_message_bytelen(
    const otcrypto_hash_mode_t hash_mode, size_t rsa_wordlen,
    size_t *max_message_bytelen) {
  // Get the hash digest length for the given hash function (and check that it
  // is one of the supported hash functions).
  size_t digest_wordlen = 0;
  HARDENED_TRY(digest_wordlen_get(hash_mode, &digest_wordlen));

  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);
  size_t rsa_bytelen = rsa_wordlen * sizeof(uint32_t);
  if (2 * digest_bytelen + 2 > rsa_bytelen) {
    // This case would cause underflow if we continue; return an error.
    return OTCRYPTO_BAD_ARGS;
  }

  *max_message_bytelen = rsa_bytelen - 2 * digest_bytelen - 2;
  return OTCRYPTO_OK;
}

status_t rsa_padding_oaep_encode(const otcrypto_hash_mode_t hash_mode,
                                 const uint8_t *message, size_t message_bytelen,
                                 const uint8_t *label, size_t label_bytelen,
                                 size_t encoded_message_len,
                                 uint32_t *encoded_message) {
  // Check that the message is not too long (RFC 8017, section 7.1.1, step 1a).
  size_t max_message_bytelen = 0;
  HARDENED_TRY(rsa_padding_oaep_max_message_bytelen(
      hash_mode, encoded_message_len, &max_message_bytelen));
  if (message_bytelen > max_message_bytelen) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get the hash digest length for the given hash function (and check that it
  // is one of the supported hash functions).
  size_t digest_wordlen = 0;
  HARDENED_TRY(digest_wordlen_get(hash_mode, &digest_wordlen));

  // Hash the label (step 2a).
  uint32_t lhash[digest_wordlen];
  HARDENED_TRY(hash(hash_mode, label, label_bytelen, lhash));

  // Generate a random string the same length as a hash digest (step 2d).
  uint32_t seed[digest_wordlen];
  HARDENED_TRY(entropy_complex_check());
  HARDENED_TRY(entropy_csrng_instantiate(
      /*disable_trng_input=*/kHardenedBoolFalse, &kEntropyEmptySeed));
  HARDENED_TRY(entropy_csrng_generate(&kEntropyEmptySeed, seed, ARRAYSIZE(seed),
                                      /*fips_check=*/kHardenedBoolTrue));
  HARDENED_TRY(entropy_csrng_uninstantiate());

  // Generate dbMask = MGF(seed, k - hLen - 1) (step 2e).
  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);
  size_t encoded_message_bytelen = encoded_message_len * sizeof(uint32_t);
  size_t db_bytelen = encoded_message_bytelen - digest_bytelen - 1;
  size_t db_wordlen = ceil_div(db_bytelen, sizeof(uint32_t));
  uint32_t db[db_wordlen];
  HARDENED_TRY(
      mgf1(hash_mode, (unsigned char *)seed, sizeof(seed), db_bytelen, db));

  // Construct maskedDB = dbMask XOR (lhash || PS || 0x01 || M), where PS is
  // all-zero (step 2f). By computing the mask first, we can simply XOR with
  // lhash, 0x01, and M, skipping PS because XOR with zero is the identity
  // function.
  for (size_t i = 0; i < ARRAYSIZE(lhash); i++) {
    db[i] ^= lhash[i];
  }
  size_t message_start_idx = db_bytelen - message_bytelen;
  unsigned char *db_bytes = (unsigned char *)db;
  db_bytes[message_start_idx - 1] ^= 0x01;
  for (size_t i = 0; i < message_bytelen; i++) {
    db_bytes[message_start_idx + i] ^= message[i];
  }

  // Compute seedMask = MGF(maskedDB, hLen) (step 2g).
  uint32_t seed_mask[digest_wordlen];
  HARDENED_TRY(mgf1(hash_mode, (unsigned char *)db, db_bytelen, digest_bytelen,
                    seed_mask));

  // Construct maskedSeed = seed XOR seedMask (step 2h).
  for (size_t i = 0; i < ARRAYSIZE(seed); i++) {
    seed[i] ^= seed_mask[i];
  }

  // Construct EM = 0x00 || maskedSeed || maskedDB (step 2i).
  unsigned char *encoded_message_bytes = (unsigned char *)encoded_message;
  encoded_message_bytes[0] = 0x00;
  memcpy(encoded_message_bytes + 1, seed, sizeof(seed));
  memcpy(encoded_message_bytes + 1 + sizeof(seed), db, sizeof(db));

  // Reverse the byte-order.
  reverse_bytes(encoded_message_len, encoded_message);
  return OTCRYPTO_OK;
}

status_t rsa_padding_oaep_decode(const otcrypto_hash_mode_t hash_mode,
                                 const uint8_t *label, size_t label_bytelen,
                                 uint32_t *encoded_message,
                                 size_t encoded_message_len, uint8_t *message,
                                 size_t *message_bytelen) {
  // Reverse the byte-order.
  reverse_bytes(encoded_message_len, encoded_message);
  *message_bytelen = 0;

  // Get the hash digest length for the given hash function (and check that it
  // is one of the supported hash functions).
  size_t digest_wordlen = 0;
  HARDENED_TRY(digest_wordlen_get(hash_mode, &digest_wordlen));

  // Extract maskedSeed from the encoded message (RFC 8017, section 7.1.2, step
  // 3b).
  uint32_t seed[digest_wordlen];
  unsigned char *encoded_message_bytes = (unsigned char *)encoded_message;
  memcpy(seed, encoded_message_bytes + 1, sizeof(seed));

  // Extract maskedDB from the encoded message (RFC 8017, section 7.1.2, step
  // 3b).
  size_t digest_bytelen = digest_wordlen * sizeof(uint32_t);
  size_t encoded_message_bytelen = encoded_message_len * sizeof(uint32_t);
  size_t db_bytelen = encoded_message_bytelen - digest_bytelen - 1;
  size_t db_wordlen = ceil_div(db_bytelen, sizeof(uint32_t));
  uint32_t db[db_wordlen];
  memcpy(db, encoded_message_bytes + 1 + sizeof(seed), db_bytelen);

  // Compute seedMask = MGF(maskedDB, hLen) (step 3c).
  uint32_t seed_mask[digest_wordlen];
  HARDENED_TRY(mgf1(hash_mode, (unsigned char *)db, db_bytelen, digest_bytelen,
                    seed_mask));

  // Construct seed = maskedSeed XOR seedMask (step 3d).
  for (size_t i = 0; i < ARRAYSIZE(seed); i++) {
    seed[i] ^= seed_mask[i];
  }

  // Generate dbMask = MGF(seed, k - hLen - 1) (step 3e).
  uint32_t db_mask[db_wordlen];
  HARDENED_TRY(mgf1(hash_mode, (unsigned char *)seed, sizeof(seed), db_bytelen,
                    db_mask));

  // Zero trailing bytes of DB and dbMask if needed.
  size_t num_trailing_bytes = sizeof(db) - db_bytelen;
  if (num_trailing_bytes > 0) {
    memset(((unsigned char *)db) + db_bytelen, 0, num_trailing_bytes);
    memset(((unsigned char *)db_mask) + db_bytelen, 0, num_trailing_bytes);
  }

  // Construct DB = dbMask XOR maskedDB.
  for (size_t i = 0; i < ARRAYSIZE(db); i++) {
    db[i] ^= db_mask[i];
  }

  // Hash the label (step 3a).
  uint32_t lhash[digest_wordlen];
  HARDENED_TRY(hash(hash_mode, label, label_bytelen, lhash));

  // Note: as we compare parts of the encoded message to their expected values,
  // we must be careful that the attacker cannot differentiate error codes or
  // get partial information about the encoded message. See the note in RCC
  // 8017, section 7.1.2. This implementation currently protects against
  // revealing this information through error codes or timing, but does not yet
  // defend against power side channels.

  // Locate the start of the message in DB = lhash || 0x00..0x00 || 0x01 || M
  // by searching for the 0x01 byte in constant time.
  unsigned char *db_bytes = (unsigned char *)db;
  uint32_t message_start_idx = 0;
  ct_bool32_t decode_failure = 0;
  for (size_t i = digest_bytelen; i < db_bytelen; i++) {
    uint32_t byte = 0;
    memcpy(&byte, db_bytes + i, 1);
    ct_bool32_t is_one = ct_seq32(byte, 0x01);
    ct_bool32_t is_before_message = ct_seqz32(message_start_idx);
    ct_bool32_t is_message_start = is_one & is_before_message;
    message_start_idx = ct_cmov32(is_message_start, i + 1, message_start_idx);
    ct_bool32_t is_zero = ct_seqz32(byte);
    ct_bool32_t padding_failure = is_before_message & (~is_zero) & (~is_one);
    decode_failure |= padding_failure;
  }
  HARDENED_CHECK_LE(message_start_idx, db_bytelen);

  // If we never found a message start index, we should fail. However, don't
  // fail yet to avoid leaking timing information.
  ct_bool32_t message_start_not_found = ct_seqz32(message_start_idx);
  decode_failure |= message_start_not_found;

  // Check that the first part of DB is equal to lhash.
  hardened_bool_t lhash_matches = hardened_memeq(lhash, db, digest_wordlen);
  ct_bool32_t lhash_match = ct_seq32(lhash_matches, kHardenedBoolTrue);
  ct_bool32_t lhash_mismatch = ~lhash_match;
  decode_failure |= lhash_mismatch;

  // Check that the leading byte is 0.
  uint32_t leading_byte = 0;
  memcpy(&leading_byte, encoded_message_bytes, 1);
  ct_bool32_t leading_byte_nonzero = ~ct_seqz32(leading_byte);
  decode_failure |= leading_byte_nonzero;

  // Now, decode_failure is all-zero if the decode succeeded and all-one if the
  // decode failed.
  if (launder32(decode_failure) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(decode_failure, 0);

  // TODO: re-check the padding as an FI hardening measure?

  // If we get here, then the encoded message has a proper format and it is
  // safe to copy the message into the output buffer.
  *message_bytelen = db_bytelen - message_start_idx;
  if (*message_bytelen > 0) {
    memcpy(message, db_bytes + message_start_idx, *message_bytelen);
  }
  return OTCRYPTO_OK;
}
