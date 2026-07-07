// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/mldsa/mldsa.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('m', 'l', 'd')

enum {
  // Size of the truncated public-key hash tr.
  kOtcryptoMldsaTrBytes = 64,
  kOtcryptoMldsaTrWords = kOtcryptoMldsaTrBytes / sizeof(uint32_t),
  // Size of the message hash mu.
  kOtcryptoMldsaMuBytes = 64,
  kOtcryptoMldsaMuWords = kOtcryptoMldsaMuBytes / sizeof(uint32_t),
  // Size of the M' buffer.
  kOtCryptoMldsaBufferBytes = 10240,
  kOtCryptoMldsaBufferWords = kOtCryptoMldsaBufferBytes / sizeof(uint32_t),
  // Maximum size of a pre-hash message digest.
  kOtcryptoMldsaPhMaxWords = 16,
};

// Lookup table for the supported pre-hash functions, indexed by their OID.
otcrypto_status_t (*hashes[16])(const otcrypto_const_byte_buf_t *,
                                otcrypto_hash_digest_t *) = {
    [0] = NULL,  // reserved
    [1] = otcrypto_sha2_256,
    [2] = otcrypto_sha2_384,
    [3] = otcrypto_sha2_512,
    [4] = NULL,  // SHA2_224 (unsupported)
    [5] = NULL,  // SHA2_512/224 (unsupported)
    [6] = NULL,  // SHA2_512/256 (unsupported)
    [7] = otcrypto_sha3_224,
    [8] = otcrypto_sha3_256,
    [9] = otcrypto_sha3_384,
    [10] = otcrypto_sha3_512,
    [11] = otcrypto_shake128,
    [12] = otcrypto_shake256,
    [13] = NULL,  // reserved
    [14] = NULL,  // reserved
    [15] = NULL,  // reserved
};

// Extract the OID and digest length from the hash function identifier, see
// the encoding of `otcrypto_mldsa_hash_mode_t`.
#define EXTRACT_HASH_OID(x) (x & 0xf)
#define EXTRACT_HASH_LEN(x) ((x >> 4) & 0xff)

// Object identifier prefix for the pre-hash mode, see
// https://csrc.nist.gov/projects/computer-security-objects-register/algorithm-registration
static const uint8_t oid_prefix[10] = {
    0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02,
};

// Check the integrity and length of an unblinded key.
static otcrypto_status_t check_unblinded_key(
    const otcrypto_unblinded_key_t *key) {
  // Integrity check.
  if (launder32(otcrypto_integrity_unblinded_key_check(key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_integrity_unblinded_key_check(key),
                    kHardenedBoolTrue);

  // Length check.
  if (key->key_length != kOtcryptoMldsa87PkBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key->key_length, kOtcryptoMldsa87PkBytes);
  return OTCRYPTO_OK;
}

// Check the integrity and length of a constant byte buffer.
static otcrypto_status_t check_byte_buf(const otcrypto_const_byte_buf_t *buf,
                                        size_t max_len) {
  // Integrity check.
  if (launder32(otcrypto_check_const_byte_buf(buf)) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_check_const_byte_buf(buf), kHardenedBoolTrue);

  // Length check.
  if (buf->len > max_len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(buf->len <= max_len, 0);
  return OTCRYPTO_OK;
}

// Check the integrity and length of a constant word32 buffer.
static otcrypto_status_t check_word32_buf(
    const otcrypto_const_word32_buf_t *buf, size_t len) {
  // Integrity check.
  if (launder32(otcrypto_check_const_word32_buf(buf)) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_check_const_word32_buf(buf), kHardenedBoolTrue);
  // Length check.
  if (buf->len != len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(buf->len == len, 0);
  return OTCRYPTO_OK;
}

/**
 * Compute the message hash mu.
 *
 * Helper function to compute the mu = Shake256(tr || M'), where M' is either
 * 0 || len(ctx) || ctx || msg in pure hash mode or
 * 1 || len(ctx) || ctx || oid || ph in pre-hash mode with ph = H(msg) for a
 * chosen hash function.
 *
 * No input checking is performed (neither NULL nor length), the calling
 * function must provide valid inputs.
 *
 * @param tr The public key hash (64 bytes).
 * @param context The context string (max 255 bytes).
 * @param message The message bytes.
 * @param hash_mode The requested hash mode, either pure or pre-hash.
 * @param mu The resulting message hash (64 bytes).
 * @return Result of the operation (OK or error).
 */
otcrypto_status_t compute_mu(const otcrypto_hash_digest_t *tr,
                             const otcrypto_const_byte_buf_t *context,
                             const otcrypto_const_byte_buf_t *message,
                             otcrypto_mldsa_hash_mode_t hash_mode,
                             otcrypto_hash_digest_t *mu) {
  // Allocate the M' buffer (10 KiB).
  // TODO: This is only temporary until we have a SHA3 streaming mode.
  uint8_t m[kOtCryptoMldsaBufferBytes];

  // Effective size of M'.
  size_t m_len = 0;

  // Copy tr into M'[0:64].
  HARDENED_TRY(randomized_bytecopy(m, tr->data, kOtcryptoMldsaTrBytes));
  m_len += kOtcryptoMldsaTrBytes;

  if (hash_mode == kOtcryptoMldsaHashModePure) {
    HARDENED_CHECK_EQ(hash_mode, kOtcryptoMldsaHashModePure);

    // M'[64] = 0.
    m[m_len] = 0;
    m_len += 1;

    // M'[65] = len(ctx).
    m[m_len] = (uint8_t)context->len;
    m_len += 1;

    // M'[66 : 66 + len(ctx)] = ctx
    HARDENED_TRY(randomized_bytecopy(m + m_len, context->data, context->len));
    m_len += context->len;

    // M'[66 + len(ctx) : 66 + len(ctx) + len(msg)] = msg.
    HARDENED_TRY(randomized_bytecopy(m + m_len, message->data, message->len));
    m_len += message->len;

  } else {
    HARDENED_CHECK_NE(hash_mode, kOtcryptoMldsaHashModePure);

    uint8_t oid_suf = EXTRACT_HASH_OID(hash_mode);
    uint8_t dig_len = EXTRACT_HASH_LEN(hash_mode);

    // Perform the hash function lookup twice and compare.
    otcrypto_status_t (*hash)(const otcrypto_const_byte_buf_t *,
                              otcrypto_hash_digest_t *) = hashes[oid_suf];
    if (hash == NULL) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_NE(hash, NULL);

    // Allocate the pre-hash buffer ph.
    uint32_t ph_data[kOtcryptoMldsaPhMaxWords];
    otcrypto_hash_digest_t ph = {
        .data = ph_data,
        .len = dig_len / sizeof(uint32_t),
    };

    // ph = hash(msg).
    HARDENED_TRY(hash(message, &ph));

    // M'[64] = 1.
    m[m_len] = 1;
    m_len += 1;

    // M'[65] = len(ctx).
    m[m_len] = (uint8_t)context->len;
    m_len += 1;

    // M'[66 : 66 + len(ctx)] = ctx
    HARDENED_TRY(randomized_bytecopy(m + m_len, context->data, context->len));
    m_len += context->len;

    // M'[66 + len(ctx) : 66 + len(ctx) + 10] = oid_prefix.
    HARDENED_TRY(randomized_bytecopy(m + m_len, oid_prefix, 10));
    m_len += 10;

    // M'[66 + len(ctx) : 66 + len(ctx) + 10] = oid_suffix.
    m[m_len] = oid_suf;
    m_len += 1;

    // M'[66 + len(ctx) + 11 : 66 + len(ctx)+ 11 + len(ph)] = ph.
    HARDENED_TRY(randomized_bytecopy(m + m_len, ph.data, dig_len));
    m_len += dig_len;
  }

  // mu = SHAKE256(tr || M').
  otcrypto_const_byte_buf_t buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, m, m_len);
  HARDENED_TRY(otcrypto_shake256(&buf, mu));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_mldsa87_keygen(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t message,
    const otcrypto_const_byte_buf_t context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_word32_buf_t signature) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_verify(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    const otcrypto_const_word32_buf_t *signature,
    otcrypto_mldsa_hash_mode_t hash_mode,
    hardened_bool_t *verification_result) {
  HARDENED_TRY(otcrypto_mldsa87_verify_async_start(public_key, message, context,
                                                   signature, hash_mode));
  return otcrypto_mldsa87_verify_async_finalize(signature, verification_result);
}

otcrypto_status_t otcrypto_mldsa87_keycheck(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keygen_async_start(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keygen_async_finalize(
    const otcrypto_unblinded_key_t *private_key,
    otcrypto_unblinded_key_t *public_key) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t message,
    const otcrypto_const_byte_buf_t context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_word32_buf_t signature) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_sign_async_finalize(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t message,
    const otcrypto_const_byte_buf_t context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_word32_buf_t signature) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_verify_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    const otcrypto_const_word32_buf_t *signature,
    otcrypto_mldsa_hash_mode_t hash_mode) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (public_key == NULL || public_key->key == NULL || message == NULL ||
      context == NULL || signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Check the integrity and length of the input buffers.
  HARDENED_TRY(check_unblinded_key(public_key));
  HARDENED_TRY(check_byte_buf(context, kOtcryptoMldsa87CtxMaxBytes));
  HARDENED_TRY(check_byte_buf(message, kOtcryptoMldsa87MsgMaxBytes));
  HARDENED_TRY(check_word32_buf(signature, kOtcryptoMldsa87SigWords));

  // Compute the public key hash tr = SHAKE256(pk, 64).

  // Convert the public key to byte buffer
  otcrypto_const_byte_buf_t pk_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const uint8_t *)public_key->key,
      public_key->key_length);

  // Allocate the 64-byte tr digest.
  uint32_t tr_data[kOtcryptoMldsaTrWords] = {0};
  otcrypto_hash_digest_t tr = {
      .data = tr_data,
      .len = kOtcryptoMldsaTrWords,
  };
  HARDENED_TRY(otcrypto_shake256(&pk_buf, &tr));

  uint32_t mu_data[kOtcryptoMldsaMuWords] = {0};
  otcrypto_hash_digest_t mu = {
      .data = mu_data,
      .len = kOtcryptoMldsaMuWords,
  };

  HARDENED_TRY(compute_mu(&tr, context, message, hash_mode, &mu));

  // Pass public key, signature and mu to the OTBN app and invoke it.
  HARDENED_TRY_WIPE_DMEM(
      mldsa87_verify_internal_start(public_key, signature, &mu));

  // Check the buffers again before exiting.
  HARDENED_TRY(check_unblinded_key(public_key));
  HARDENED_TRY(check_byte_buf(context, kOtcryptoMldsa87CtxMaxBytes));
  HARDENED_TRY(check_byte_buf(message, kOtcryptoMldsa87MsgMaxBytes));
  HARDENED_TRY(check_word32_buf(signature, kOtcryptoMldsa87SigWords));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mldsa87_verify_async_finalize(
    const otcrypto_const_word32_buf_t *signature,
    hardened_bool_t *verification_result) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY(check_word32_buf(signature, kOtcryptoMldsa87SigWords));

  return otcrypto_eval_exit(
      mldsa87_verify_internal_finalize(signature, verification_result));
}

otcrypto_status_t otcrypto_mldsa87_keycheck_async_start(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

otcrypto_status_t otcrypto_mldsa87_keycheck_async_finalize(
    const otcrypto_unblinded_key_t *public_key,
    const otcrypto_blinded_key_t *private_key,
    hardened_bool_t *keycheck_result) {
  // TODO: Connect ML-DSA operations to API.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
