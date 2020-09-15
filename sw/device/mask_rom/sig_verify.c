// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/mask_rom/sig_verify.h"

#include <memory.h>

#include "sw/device/lib/common.h"

/**
 * A key ID.
 *
 * Note: Key IDs are assigned manually and are guaranteed to be unique.
 */
typedef uint32_t sig_verify_key_id_t;

/**
 * Block type.
 */
typedef enum sig_verify_block_type {
  kSigVerifyBlockType0,
  kSigVerifyBlockType1,
} sig_verify_block_type_t;

/**
 * Supported RSA key lengths.
 */
typedef enum sig_verify_rsa_key_length {
  kSigVerifyRsaKeyLength2k,
  kSigVerifyRsaKeyLength3k,
} sig_verify_rsa_key_length_t;

/**
 * An octet string of length k that can be used to represent moduli, signatures,
 * and encryption blocks for RSA keys that are k octets long.
 */
typedef struct sig_verify_rsa_octet_string {
  sig_verify_rsa_key_length_t key_length;
  union {
    uint8_t rsa2k[256];
    uint8_t rsa3k[384];
  };
} sig_verify_rsa_octet_string_t;

/**
 * An RSA public key.
 */
typedef struct sig_verify_public_key {
  sig_verify_key_id_t key_id;
  sig_verify_rsa_octet_string_t modulus;
  uint32_t exponent;
} sig_verify_public_key_t;

/**
 * Check if two digests are equal.
 *
 * Two digests are equal if they are calculated using the same hash algorithm
 * and have the same value.
 */
static sig_verify_result_t sig_verify_digests_are_equal(
    sig_verify_digest_t const *lhs, sig_verify_digest_t const *rhs,
    bool *are_equal) {
  if (lhs == NULL || rhs == NULL || are_equal == NULL) {
    return kSigVerifyError;
  }
  // Not equal unless all checks are successful.
  *are_equal = false;
  // Compare hash algorithms.
  if (lhs->alg != rhs->alg) {
    return kSigVerifyOk;
  }
  const uint8_t *lhs_value;
  size_t lhs_length;
  const uint8_t *rhs_value;
  size_t rhs_length;
  // Get the bytes of LHS and RHS.
  // This can fail if we encounter an unsupported hash algorithm.
  if (sig_verify_get_digest_value(lhs, &lhs_value, &lhs_length) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }
  if (sig_verify_get_digest_value(rhs, &rhs_value, &rhs_length) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }
  // Compare lengths.
  if (lhs_length != rhs_length) {
    return kSigVerifyOk;
  }
  // Compare bytes.
  if (memcmp(lhs_value, rhs_value, lhs_length) != 0) {
    return kSigVerifyOk;
  }
  // Digests are equal.
  *are_equal = true;
  return kSigVerifyOk;
}

/**
 * Returns the key with the given ID.
 *
 * A key with the given ID must exist and be allowed to be used.
 */
static sig_verify_result_t sig_verify_get_key_by_id(
    sig_verify_key_id_t key_id, sig_verify_public_key_t *key) {
  // TODO: jon-flatley
  return kSigVerifyOk;
}

static sig_verify_result_t sig_verify_get_rsa_octet_string_value(
    const sig_verify_rsa_octet_string_t *octet_string, const uint8_t **value,
    size_t *length) {
  if (octet_string == NULL || value == NULL || length == NULL) {
    return kSigVerifyError;
  }
  switch (octet_string->key_length) {
    case kSigVerifyRsaKeyLength2k:
      *value = octet_string->rsa2k;
      *length = ARRAYSIZE(octet_string->rsa2k);
      break;
    case kSigVerifyRsaKeyLength3k:
      *value = octet_string->rsa3k;
      *length = ARRAYSIZE(octet_string->rsa3k);
      break;
    default:
      return kSigVerifyError;
  }
  return kSigVerifyOk;
}

static sig_verify_result_t sig_verify_perform_rsa(
    const sig_verify_public_key_t *key,
    const sig_verify_rsa_octet_string_t *signature,
    sig_verify_rsa_octet_string_t *enc_block) {
  if (key == NULL || signature == NULL || enc_block == NULL) {
    return kSigVerifyError;
  }
  // TODO: jon-flatley
  // Get signature bytes.
  const uint8_t *sig;
  size_t sig_len;
  if (sig_verify_get_rsa_octet_string_value(signature, &sig, &sig_len) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }
  // Get modulus from public key.
  const uint8_t *mod;
  size_t mod_len;
  if (sig_verify_get_rsa_octet_string_value(&key->modulus, &mod, &mod_len) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }
  // Modulus and signature must have the same length.
  if (mod_len != sig_len) {
    return kSigVerifyError;
  }

  // Perform RSA computation to obtain the encryption block
  // TODO: jon-flatley

  return kSigVerifyOk;
}

static sig_verify_result_t sig_verify_decode_enc_block(
    const sig_verify_rsa_octet_string_t *enc_block,
    sig_verify_digest_t *digest) {
  // TODO: alphan
  // Parse encryption block and decode data
  //   - Parse padding
  //   - Decode the encoded message to get digest and hash alg
  return kSigVerifyOk;
}

static sig_verify_result_t sig_verify_get_digest_from_signature(
    const sig_verify_public_key_t *key,
    const sig_verify_rsa_octet_string_t *signature,
    sig_verify_digest_t *digest) {
  if (key == NULL || signature == NULL || digest == NULL) {
    return kSigVerifyError;
  }

  // Perform RSA computation to obtain the encryption block.
  sig_verify_rsa_octet_string_t enc_block;
  if (sig_verify_perform_rsa(key, signature, &enc_block) != kSigVerifyOk) {
    return kSigVerifyError;
  }

  // Decode the encryption block to obtain the expected digest.
  if (sig_verify_decode_enc_block(&enc_block, digest) != kSigVerifyOk) {
    return kSigVerifyError;
  }

  return kSigVerifyOk;
}

static sig_verify_result_t sig_verify_get_manifest_signature(
    const rom_ext_manifest_t *manifest, sig_verify_rsa_octet_string_t *sig) {
  // TODO: alphan
  // This will probably be provided by the ROM_EXT Manifest module.
  // - Get signature alg from manifest
  //   - Return error if not supported
  // - Get signature from manifest
  //   - Length determined by signature algorithm or always RSA3072?
  return kSigVerifyOk;
}

static sig_verify_result_t sig_verify_hash_manifest(
    const rom_ext_manifest_t *manifest, sig_verify_hash_alg_t hash_alg,
    sig_verify_digest_t *digest) {
  // TODO: jon-flatley
  return kSigVerifyOk;
}

sig_verify_result_t sig_verify_verify_rom_ext(
    const rom_ext_manifest_t *manifest, bool *is_valid,
    sig_verify_digest_t *actual, sig_verify_digest_t *expected) {
  if (manifest == NULL || is_valid == NULL) {
    return kSigVerifyError;
  }

  // Get the key to be used to verify the manifest.
  sig_verify_public_key_t key;
  if (sig_verify_get_key_by_id(manifest->key_id, &key) != kSigVerifyOk) {
    return kSigVerifyError;
  }

  // Get the signature of the manifest.
  sig_verify_rsa_octet_string_t sig;
  if (sig_verify_get_manifest_signature(manifest, &sig) != kSigVerifyOk) {
    return kSigVerifyError;
  }

  // Get expected digest from signature.
  sig_verify_digest_t exp_digest;
  if (sig_verify_get_digest_from_signature(&key, &sig, &exp_digest) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }

  // Hash ROM_EXT manifest.
  sig_verify_digest_t act_digest;
  if (sig_verify_hash_manifest(manifest, exp_digest.alg, &act_digest) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }

  // Compare actual and expected digests.
  if (sig_verify_digests_are_equal(&exp_digest, &act_digest, is_valid) !=
      kSigVerifyOk) {
    return kSigVerifyError;
  }

  // Output actual and expected digests if requested.
  if (actual) {
    *actual = act_digest;
  }
  if (expected) {
    *expected = exp_digest;
  }

  return kSigVerifyOk;
}

sig_verify_result_t sig_verify_get_digest_value(
    const sig_verify_digest_t *digest, const uint8_t **value, size_t *length) {
  if (digest == NULL || value == NULL || length == NULL) {
    return kSigVerifyError;
  }

  switch (digest->alg) {
    case kSigVerifyHashAlgSha2_256:
      *value = digest->sha2_256;
      *length = ARRAYSIZE(digest->sha2_256);
    case kSigVerifyHashAlgSha2_384:
      *value = digest->sha2_384;
      *length = ARRAYSIZE(digest->sha2_384);
    case kSigVerifyHashAlgSha2_512:
      *value = digest->sha2_512;
      *length = ARRAYSIZE(digest->sha2_512);
    default:
      return kSigVerifyError;
  }

  return kSigVerifyOk;
}
