// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/rsa/rsa_signature.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_modexp.h"
#include "sw/device/lib/crypto/impl/rsa/rsa_padding.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/include/hash.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 's', 'v')

/**
 * Constant empty seed material for the entropy complex.
 */
static const entropy_seed_material_t kEntropyEmptySeed = {
    .len = 0,
    .data = {0},
};

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
static status_t digest_check(const hash_digest_t *digest) {
  size_t num_words = 0;
  switch (digest->mode) {
    case kHashModeSha3_224:
      num_words = 224 / 32;
      break;
    case kHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_256:
      num_words = 256 / 32;
      break;
    case kHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_384:
      num_words = 384 / 32;
      break;
    case kHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_512:
      num_words = 512 / 32;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(num_words, 0);

  if (num_words != digest->len) {
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
static status_t message_encode(const hash_digest_t *message_digest,
                               const rsa_signature_padding_t padding_mode,
                               size_t encoded_message_len,
                               uint32_t *encoded_message) {
  // Check that the digest length is OK.
  HARDENED_TRY(digest_check(message_digest));

  switch (padding_mode) {
    case kRsaSignaturePaddingPkcs1v15:
      return rsa_padding_pkcs1v15_encode(message_digest, encoded_message_len,
                                         encoded_message);
    case kRsaSignaturePaddingPss: {
      // Generate a random salt value whose length matches the digest length.
      uint32_t salt[message_digest->len];
      HARDENED_TRY(entropy_complex_check());
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
 * @param encoded_message_len Encoded message length in 32-bit words.
 * @param[out] result True if the check passed.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
static status_t encoded_message_verify(
    const hash_digest_t *message_digest,
    const rsa_signature_padding_t padding_mode, uint32_t *encoded_message,
    const size_t encoded_message_len, hardened_bool_t *result) {
  // Check that the digest length is OK.
  HARDENED_TRY(digest_check(message_digest));

  switch (padding_mode) {
    case kRsaSignaturePaddingPkcs1v15:
      return rsa_padding_pkcs1v15_verify(message_digest, encoded_message,
                                         encoded_message_len, result);
    case kRsaSignaturePaddingPss:
      return rsa_padding_pss_verify(message_digest, encoded_message,
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
  HARDENED_TRY(message_encode(message_digest, padding_mode,
                              ARRAYSIZE(encoded_message.data),
                              encoded_message.data));

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
          ARRAYSIZE(recovered_message.data), verification_result);
    }
    case kRsa3072NumWords: {
      rsa_3072_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_3072_finalize(&recovered_message));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          ARRAYSIZE(recovered_message.data), verification_result);
    }
    case kRsa4096NumWords: {
      rsa_4096_int_t recovered_message;
      HARDENED_TRY(rsa_modexp_4096_finalize(&recovered_message));
      return encoded_message_verify(
          message_digest, padding_mode, recovered_message.data,
          ARRAYSIZE(recovered_message.data), verification_result);
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
  HARDENED_TRY(message_encode(message_digest, padding_mode,
                              ARRAYSIZE(encoded_message.data),
                              encoded_message.data));

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
  HARDENED_TRY(message_encode(message_digest, padding_mode,
                              ARRAYSIZE(encoded_message.data),
                              encoded_message.data));

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
