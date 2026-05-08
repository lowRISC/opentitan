// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_padding.h"
#include "sw/device/lib/crypto/impl/rsa/run_rsa.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 's', 'v')

/**
 * Ensure that the digest type matches the length and is supported.
 *
 * Accepts only SHA-2 and SHA-3 family hash functions (XOFs such as SHAKE are
 * not currently supported for RSA). Returns an error if the digest type is
 * unsupported or the digest buffer is the wrong length.
 *
 * @param digest Message digest to check.
 * @return Result of the operation (OK or BAD_ARGS).
 */
OT_WARN_UNUSED_RESULT
static status_t digest_check(const otcrypto_hash_digest_t digest) {
  size_t num_words = 0;
  otcrypto_hash_mode_t used_mode = launder32(0);
  switch (digest.mode) {
    case kOtcryptoHashModeSha3_224:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha3_224;
      num_words = 224 / 32;
      break;
    case kOtcryptoHashModeSha256:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha256;
      num_words = 256 / 32;
      break;
    case kOtcryptoHashModeSha3_256:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha3_256;
      num_words = 256 / 32;
      break;
    case kOtcryptoHashModeSha384:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha384;
      num_words = 384 / 32;
      break;
    case kOtcryptoHashModeSha3_384:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha3_384;
      num_words = 384 / 32;
      break;
    case kOtcryptoHashModeSha512:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha512;
      num_words = 512 / 32;
      break;
    case kOtcryptoHashModeSha3_512:
      used_mode = launder32(used_mode) | kOtcryptoHashModeSha3_512;
      num_words = 512 / 32;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(num_words, 0);
  HARDENED_CHECK_EQ(launder32(used_mode), digest.mode);

  if (num_words != digest.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Encode the message with the provided padding mode and hash function.
 *
 * @param message_digest Message digest to encode.
 * @param padding_mode Signature padding mode.
 * @param encoded_message_len Encoded message length in 32-bit words.
 * @param[out] encoded_message Encoded message.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
static status_t message_encode(const otcrypto_hash_digest_t message_digest,
                               const rsa_signature_padding_t padding_mode,
                               size_t encoded_message_len,
                               uint32_t *encoded_message) {
  // Check that the digest length is OK.
  HARDENED_TRY(digest_check(message_digest));

  switch (launder32(padding_mode)) {
    case kRsaSignaturePaddingPkcs1v15:
      HARDENED_CHECK_EQ(padding_mode, kRsaSignaturePaddingPkcs1v15);
      return rsa_padding_pkcs1v15_encode(message_digest, encoded_message_len,
                                         encoded_message);
    case kRsaSignaturePaddingPss: {
      HARDENED_CHECK_EQ(padding_mode, kRsaSignaturePaddingPss);
      // Generate a random salt value whose length matches the digest length.
      uint32_t salt[message_digest.len];
      HARDENED_TRY(entropy_csrng_uninstantiate());
      HARDENED_TRY(entropy_csrng_instantiate(
          /*disable_trng_input=*/kHardenedBoolFalse, &kEntropyEmptySeed));
      HARDENED_TRY(entropy_csrng_generate(&kEntropyEmptySeed, salt,
                                          ARRAYSIZE(salt),
                                          /*fips_check=*/kHardenedBoolTrue));
      HARDENED_TRY(entropy_csrng_uninstantiate());
      return rsa_padding_pss_encode(message_digest, salt, ARRAYSIZE(salt),
                                    encoded_message_len, encoded_message);
    }
    default:
      // Unrecognized padding mode.
      // COVERAGE (MISSING) We only provide inputs with correct padding modes.
      return OTCRYPTO_BAD_ARGS;
  }

  // Unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
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
 * @param encoded_message_len Encoded message length in 32-bit words.
 * @param[out] result True if the check passed.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
static status_t encoded_message_verify(
    const otcrypto_hash_digest_t message_digest,
    const rsa_signature_padding_t padding_mode, uint32_t *encoded_message,
    const size_t encoded_message_len, hardened_bool_t *result) {
  // Check that the digest length is OK.
  HARDENED_TRY(digest_check(message_digest));

  switch (launder32(padding_mode)) {
    case kRsaSignaturePaddingPkcs1v15:
      HARDENED_CHECK_EQ(padding_mode, kRsaSignaturePaddingPkcs1v15);
      return rsa_padding_pkcs1v15_verify(message_digest, encoded_message,
                                         encoded_message_len, result);
    case kRsaSignaturePaddingPss:
      HARDENED_CHECK_EQ(padding_mode, kRsaSignaturePaddingPss);
      return rsa_padding_pss_verify(message_digest, encoded_message,
                                    encoded_message_len, result);
    default:
      // Unrecognized padding mode.
      // COVERAGE (MISSING) We only provide inputs with correct padding modes.
      return OTCRYPTO_BAD_ARGS;
  }

  // Unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}

status_t rsa_signature_generate_start(
    rsa_size_t size, const uint32_t *d0, const uint32_t *d1, const uint32_t *n,
    const otcrypto_hash_digest_t message_digest,
    const rsa_signature_padding_t padding_mode) {
  size_t num_words = 0;
  switch (launder32(size)) {
    case kRsaSize2048:
      HARDENED_CHECK_EQ(size, kRsaSize2048);
      num_words = kRsa2048NumWords;
      break;
    case kRsaSize3072:
      HARDENED_CHECK_EQ(size, kRsaSize3072);
      num_words = kRsa3072NumWords;
      break;
    case kRsaSize4096:
      HARDENED_CHECK_EQ(size, kRsaSize4096);
      num_words = kRsa4096NumWords;
      break;
    default:
      HARDENED_TRAP();
      // COVERAGE (FI CM) Unreachable code, checked against fault injections.
      return OTCRYPTO_FATAL_ERR;
  }

  // Allocate maximum possible size to avoid VLAs. We allocate enough for
  // 4096, but will only utilize `num_words`.
  uint32_t encoded_message[kRsa4096NumWords];
  HARDENED_TRY(hardened_memshred(encoded_message, ARRAYSIZE(encoded_message)));

  // Encode the message.
  HARDENED_TRY(
      message_encode(message_digest, padding_mode, num_words, encoded_message));

  // Start computing (encoded_message ^ d) mod n.
  return rsa_modexp_consttime_start(size, encoded_message, d0, d1, n);
}

status_t rsa_signature_generate_finalize(rsa_size_t size, uint32_t *signature) {
  return rsa_modexp_finalize_size(size, signature);
}

status_t rsa_signature_verify_start(rsa_size_t size, const uint32_t *n,
                                    const uint32_t *signature) {
  // Start computing (sig ^ e) mod n with a variable-time exponentiation.
  return rsa_modexp_vartime_start(size, signature, n);
}

status_t rsa_signature_verify_finalize(
    const otcrypto_hash_digest_t message_digest,
    const rsa_signature_padding_t padding_mode,
    hardened_bool_t *verification_result) {
  // Wait for OTBN to complete and get the size for the last RSA operation.
  size_t num_words;
  HARDENED_TRY(rsa_modexp_wait(&num_words));

  // Call the appropriate `finalize()` operation to get the recovered encoded
  // message.
  switch (launder32(num_words)) {
    case kRsa2048NumWords: {
      HARDENED_CHECK_EQ(num_words, kRsa2048NumWords);
      rsa_2048_int_t recovered_message;
      HARDENED_TRY(
          rsa_modexp_finalize_size(kRsaSize2048, recovered_message.data));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          ARRAYSIZE(recovered_message.data), verification_result);
    }
    case kRsa3072NumWords: {
      HARDENED_CHECK_EQ(num_words, kRsa3072NumWords);
      rsa_3072_int_t recovered_message;
      HARDENED_TRY(
          rsa_modexp_finalize_size(kRsaSize3072, recovered_message.data));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          ARRAYSIZE(recovered_message.data), verification_result);
    }
    case kRsa4096NumWords: {
      HARDENED_CHECK_EQ(num_words, kRsa4096NumWords);
      rsa_4096_int_t recovered_message;
      HARDENED_TRY(
          rsa_modexp_finalize_size(kRsaSize4096, recovered_message.data));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          ARRAYSIZE(recovered_message.data), verification_result);
    }
    default:
      // Unexpected number of words; should never get here.
      // COVERAGE (SW ERR) This is an internal function that is only given
      // correctly encoded inputs.
      return OTCRYPTO_FATAL_ERR;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  // COVERAGE (FI CM) Unreachable code, checked against fault injections.
  return OTCRYPTO_FATAL_ERR;
}
