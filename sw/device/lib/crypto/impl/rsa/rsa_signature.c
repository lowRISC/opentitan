// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_modexp.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 's', 'v')

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

/**
 * Encode the message with PKCS#1 v1.5 encoding (RFC 8017, section 9.2).
 *
 * The caller must ensure that `encoded_message_len` bytes are allocated in the
 * output buffer.
 *
 * We encode the message in reversed byte-order from the RFC because OTBN
 * interprets the message as a fully little-endian integer.
 *
 * @param message_digest Message digest to encode.
 * @param encoded_message_len Intended byte-length of the encoded message.
 * @param[out] encoded_message Encoded message.
 * @result Result of the operation (OK or error).
 */
static status_t pkcs1v15_encode(const hash_digest_t *message_digest,
                                size_t encoded_message_len,
                                uint32_t *encoded_message) {
  // Initialize all bits of the encoded message to 1.
  memset(encoded_message, 0xff, encoded_message_len);

  // Get a byte-sized pointer to the encoded message data.
  unsigned char *buf = (unsigned char *)encoded_message;

  // Set the last byte to 0x00 and the second-to-last byte to 0x01.
  buf[encoded_message_len - 1] = 0x00;
  buf[encoded_message_len - 2] = 0x01;

  // Get the length of the digest info (called T in the RFC).
  size_t tlen;
  HARDENED_TRY(digest_info_length_get(message_digest->mode, &tlen));

  if (tlen + 3 + 8 >= encoded_message_len) {
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

/**
 * Check if the PKCS#1 v1.5 encoded message represents the message.
 *
 * If the encoded message does not match the message, this function will return
 * an OK status and write `kHardenedBoolFalse` into the result buffer. The
 * caller should not interpret an OK status as a match between the encoded and
 * raw messages, since the status return value is reserved for operational or
 * logical error codes.
 *
 * Since PKCS#1 v1.5 padding is deterministic, we verify by re-encoding the
 * message and comparing the result.
 *
 * @param message_digest Message digest to verify.
 * @param encoded_message Encoded message.
 * @param encoded_message_len Encoded message length in bytes.
 * @param[out] result True if the check passed.
 * @result Result of the operation (OK or error).
 */
static status_t pkcs1v15_encoded_message_verify(
    const hash_digest_t *message_digest, const uint32_t *encoded_message,
    const size_t encoded_message_len, hardened_bool_t *result) {
  // Ensure that the encoded message length is divisible by the word size.
  if (encoded_message_len % sizeof(uint32_t) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Re-encode the message.
  uint32_t expected_encoded_message[encoded_message_len / sizeof(uint32_t)];
  HARDENED_TRY(pkcs1v15_encode(message_digest, encoded_message_len,
                               expected_encoded_message));

  // Compare with the expected value.
  *result = hardened_memeq(encoded_message, expected_encoded_message,
                           ARRAYSIZE(expected_encoded_message));
  return OTCRYPTO_OK;
}

/**
 * Encode the message with PSS encoding (RFC 8017, section 9.1.1).
 *
 * The caller must ensure that `encoded_message_len` bytes are allocated in the
 * output buffer.
 *
 * @param message_digest Message digest to encode.
 * @param encoded_message_len Intended byte-length of the encoded message.
 * @param[out] encoded_message Encoded message.
 * @result Result of the operation (OK or error).
 */
static status_t pss_encode(const hash_digest_t *message_digest,
                           size_t encoded_message_len,
                           uint32_t *encoded_message) {
  // TODO
  return OTCRYPTO_NOT_IMPLEMENTED;
}

/**
 * Check if the PSS-encoded message matches message (RFC 8017, section 9.1.2).
 *
 * If the encoded message does not match the message, this function will return
 * an OK status and write `kHardenedBoolFalse` into the result buffer. The
 * caller should not interpret an OK status as a match between the encoded and
 * raw messages, since the status return value is reserved for operational or
 * logical error codes.
 *
 * @param message_digest Message digest to verify.
 * @param encoded_message Encoded message.
 * @param encoded_message_len Encoded message length in bytes.
 * @param[out] result True if the check passed.
 * @result Result of the operation (OK or error).
 */
static status_t pss_encoded_message_verify(const hash_digest_t *message_digest,
                                           const uint32_t *encoded_message,
                                           const size_t encoded_message_len,
                                           hardened_bool_t *result) {
  // TODO
  return OTCRYPTO_NOT_IMPLEMENTED;
}

/**
 * Encode the message with the provided padding mode and hash function.
 *
 * @param message_digest Message digest to encode.
 * @param padding_mode Signature padding mode.
 * @param encoded_message_len Encoded message length in bytes.
 * @param[out] encoded_message Encoded message.
 * @result Result of the operation (OK or error).
 */
static status_t message_encode(const hash_digest_t *message_digest,
                               const rsa_signature_padding_t padding_mode,
                               size_t encoded_message_len,
                               uint32_t *encoded_message) {
  switch (padding_mode) {
    case kRsaSignaturePaddingPkcs1v15:
      return pkcs1v15_encode(message_digest, encoded_message_len,
                             encoded_message);
    case kRsaSignaturePaddingPss:
      return pss_encode(message_digest, encoded_message_len, encoded_message);
    default:
      // Unrecognized padding mode.
      return OTCRYPTO_BAD_ARGS;
  }

  // Unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

/**
 * Check if the encoded message represents the message.
 *
 * If the encoded message does not match the message, this function will return
 * an OK status and write `kHardenedBoolFalse` into the result buffer. The
 * caller should not interpret an OK status as a match between the encoded and
 * raw messages, since the status return value is reserved for operational or
 * logical error codes.
 *
 * @param message_digest Message digest to verify.
 * @param padding_mode Signature padding mode.
 * @param encoded_message Encoded message.
 * @param encoded_message_len Encoded message length in bytes.
 * @param[out] result True if the check passed.
 * @result Result of the operation (OK or error).
 */
static status_t encoded_message_verify(
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode, const uint32_t *encoded_message,
    const size_t encoded_message_len, hardened_bool_t *result) {
  switch (padding_mode) {
    case kRsaSignaturePaddingPkcs1v15:
      return pkcs1v15_encoded_message_verify(message_digest, encoded_message,
                                             encoded_message_len, result);
    case kRsaSignaturePaddingPss:
      return pss_encoded_message_verify(message_digest, encoded_message,
                                        encoded_message_len, result);
    default:
      // Unrecognized padding mode.
      return OTCRYPTO_BAD_ARGS;
  }

  // Unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

status_t rsa_signature_generate_2048_start(
    const rsa_2048_private_key_t *private_key,
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode) {
  // Encode the message.
  rsa_2048_int_t encoded_message;
  message_encode(message_digest, padding_mode, sizeof(encoded_message.data),
                 encoded_message.data);

  // Start computing (encoded_message ^ d) mod n.
  return rsa_modexp_consttime_2048_start(&encoded_message, &private_key->d,
                                         &private_key->n);
}

status_t rsa_signature_generate_2048_finalize(rsa_2048_int_t *signature) {
  return rsa_modexp_2048_finalize(signature);
}

status_t rsa_signature_verify_2048_start(
    const rsa_2048_public_key_t *public_key, const rsa_2048_int_t *signature) {
  // Start computing (sig ^ e) mod n with a variable-time exponentiation.
  return rsa_modexp_vartime_2048_start(signature, public_key->e,
                                       &public_key->n);
}

status_t rsa_signature_verify_finalize(
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode,
    hardened_bool_t *verification_result) {
  // Wait for OTBN to complete and get the size for the last RSA operation.
  size_t num_words;
  HARDENED_TRY(rsa_modexp_wait(&num_words));

  // Call the appropriate `finalize()` operation to get the recovered encoded
  // message.
  switch (num_words) {
    case kRsa2048NumWords: {
      rsa_2048_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_2048_finalize(&recovered_message));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          sizeof(recovered_message.data), verification_result);
    }
    case kRsa3072NumWords: {
      rsa_3072_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_3072_finalize(&recovered_message));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          sizeof(recovered_message.data), verification_result);
    }
    case kRsa4096NumWords: {
      rsa_4096_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_4096_finalize(&recovered_message));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          sizeof(recovered_message.data), verification_result);
    }
    default:
      // Unexpected number of words; should never get here.
      return OTCRYPTO_FATAL_ERR;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

status_t rsa_signature_generate_3072_start(
    const rsa_3072_private_key_t *private_key,
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode) {
  // Encode the message.
  rsa_3072_int_t encoded_message;
  message_encode(message_digest, padding_mode, sizeof(encoded_message.data),
                 encoded_message.data);

  // Start computing (encoded_message ^ d) mod n.
  return rsa_modexp_consttime_3072_start(&encoded_message, &private_key->d,
                                         &private_key->n);
}

status_t rsa_signature_generate_3072_finalize(rsa_3072_int_t *signature) {
  return rsa_modexp_3072_finalize(signature);
}

status_t rsa_signature_verify_3072_start(
    const rsa_3072_public_key_t *public_key, const rsa_3072_int_t *signature) {
  // Start computing (sig ^ e) mod n with a variable-time exponentiation.
  return rsa_modexp_vartime_3072_start(signature, public_key->e,
                                       &public_key->n);
}

status_t rsa_signature_generate_4096_start(
    const rsa_4096_private_key_t *private_key,
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode) {
  // Encode the message.
  rsa_4096_int_t encoded_message;
  message_encode(message_digest, padding_mode, sizeof(encoded_message.data),
                 encoded_message.data);

  // Start computing (encoded_message ^ d) mod n.
  return rsa_modexp_consttime_4096_start(&encoded_message, &private_key->d,
                                         &private_key->n);
}

status_t rsa_signature_generate_4096_finalize(rsa_4096_int_t *signature) {
  return rsa_modexp_4096_finalize(signature);
}

status_t rsa_signature_verify_4096_start(
    const rsa_4096_public_key_t *public_key, const rsa_4096_int_t *signature) {
  // Start computing (sig ^ e) mod n with a variable-time exponentiation.
  return rsa_modexp_vartime_4096_start(signature, public_key->e,
                                       &public_key->n);
}
