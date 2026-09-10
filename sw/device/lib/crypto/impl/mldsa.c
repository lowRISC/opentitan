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
  // Maximum size of a pre-hash message digest.
  kOtcryptoMldsaPhMaxWords = 16,
  // Size of the rnd string.
  kOtcryptoMldsaRndBytes = 32,
  kOtcryptoMldsaRndWords = kOtcryptoMldsaRndBytes / sizeof(uint32_t),
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

// Check the integrity and length of a blinded key.
static otcrypto_status_t check_blinded_key(const otcrypto_blinded_key_t *key) {
  // Integrity check.
  if (launder32(otcrypto_integrity_blinded_key_check(key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_integrity_blinded_key_check(key),
                    kHardenedBoolTrue);

  // Length check.
  if (key->keyblob_length != kOtcryptoMldsa87SkBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key->keyblob_length, kOtcryptoMldsa87SkBytes);
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
  // In pre-hash mode, first compute ph = H(msg).
  uint32_t ph_data[kOtcryptoMldsaPhMaxWords];
  uint8_t oid_suf = 0;
  uint8_t dig_len = 0;
  if (hash_mode != kOtcryptoMldsaHashModePure) {
    oid_suf = EXTRACT_HASH_OID(hash_mode);
    dig_len = EXTRACT_HASH_LEN(hash_mode);

    otcrypto_status_t (*hash)(const otcrypto_const_byte_buf_t *,
                              otcrypto_hash_digest_t *) = hashes[oid_suf];
    if (hash == NULL) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_NE(hash, NULL);

    otcrypto_hash_digest_t ph = {
        .data = ph_data,
        .len = dig_len / sizeof(uint32_t),
    };

    // ph = hash(msg).
    HARDENED_TRY(hash(message, &ph));
  }

  // mu = SHAKE256(tr || M').
  otcrypto_sha3_context_t sha3_ctx;
  HARDENED_TRY(otcrypto_shake256_init(&sha3_ctx));

  // Absorb tr.
  otcrypto_const_byte_buf_t tr_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)tr->data,
                        kOtcryptoMldsaTrBytes);
  HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, &tr_buf));

  // Absorb M'[0] (0 in pure hash mode, 1 in pre-hash mode) and
  // M'[1] = len(ctx).
  uint8_t header[2] = {hash_mode != kOtcryptoMldsaHashModePure,
                       (uint8_t)context->len};
  otcrypto_const_byte_buf_t header_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, header, sizeof(header));
  HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, &header_buf));

  // Absorb M'[2 : 2 + len(ctx)] = ctx.
  HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, context));

  if (hash_mode == kOtcryptoMldsaHashModePure) {
    HARDENED_CHECK_EQ(hash_mode, kOtcryptoMldsaHashModePure);

    // Absorb M'[2 + len(ctx) : 2 + len(ctx) + len(msg)] = msg.
    HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, message));
  } else {
    HARDENED_CHECK_NE(hash_mode, kOtcryptoMldsaHashModePure);

    // Absorb M'[2 + len(ctx) : 2 + len(ctx) + 11] = oid_prefix || oid_suffix.
    otcrypto_const_byte_buf_t oid_prefix_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, oid_prefix, sizeof(oid_prefix));
    HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, &oid_prefix_buf));

    otcrypto_const_byte_buf_t oid_suf_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &oid_suf, 1);
    HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, &oid_suf_buf));

    // Absorb M'[2 + len(ctx) + 11 : 2 + len(ctx) + 11 + len(ph)] = ph.
    otcrypto_const_byte_buf_t ph_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, (unsigned char *)ph_data, dig_len);
    HARDENED_TRY(otcrypto_sha3_update(&sha3_ctx, &ph_buf));
  }

  // Squeeze out mu.
  HARDENED_TRY(otcrypto_shake256_final(&sha3_ctx, mu));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_mldsa87_keygen(otcrypto_unblinded_key_t *public_key,
                                          otcrypto_blinded_key_t *private_key) {
  HARDENED_TRY(otcrypto_mldsa87_keygen_async_start());
  HARDENED_TRY(otcrypto_mldsa87_keygen_async_finalize(public_key, private_key));

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_mldsa87_sign(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    otcrypto_mldsa_hash_mode_t hash_mode, otcrypto_mldsa_sign_mode_t sign_mode,
    otcrypto_word32_buf_t *signature) {
  HARDENED_TRY(otcrypto_mldsa87_sign_async_start(private_key, message, context,
                                                 hash_mode, sign_mode));
  HARDENED_TRY(otcrypto_mldsa87_double_sign_async_finalize(signature));

  return OTCRYPTO_OK;
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

otcrypto_status_t otcrypto_mldsa87_keygen_async_start(void) {
  HARDENED_TRY_WIPE_DMEM(mldsa87_keygen_internal_start());

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mldsa87_keygen_async_finalize(
    otcrypto_unblinded_key_t *public_key, otcrypto_blinded_key_t *private_key) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (public_key == NULL || public_key->key == NULL || private_key == NULL ||
      private_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(
      mldsa87_keygen_internal_finalize(public_key, private_key));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mldsa87_sign_async_start(
    const otcrypto_blinded_key_t *private_key,
    const otcrypto_const_byte_buf_t *message,
    const otcrypto_const_byte_buf_t *context,
    otcrypto_mldsa_hash_mode_t hash_mode,
    otcrypto_mldsa_sign_mode_t sign_mode) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (private_key == NULL || private_key->keyblob == NULL || message == NULL ||
      context == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Check the integrity and length of the input buffers.
  HARDENED_TRY(check_blinded_key(private_key));
  HARDENED_TRY(check_byte_buf(context, kOtcryptoMldsa87CtxMaxBytes));
  HARDENED_TRY(check_byte_buf(message, kOtcryptoMldsa87MsgMaxBytes));

  // Allocate the 64-byte mu digest.
  uint32_t mu_data[kOtcryptoMldsaMuWords] = {0};
  otcrypto_hash_digest_t mu = {
      .data = mu_data,
      .len = kOtcryptoMldsaMuWords,
  };

  // Extract tr from the secret key.
  otcrypto_hash_digest_t tr = {
      .data = private_key->keyblob + 24,
      .len = kOtcryptoMldsaTrWords,
  };

  // mu = Shake256(tr || M').
  HARDENED_TRY(compute_mu(&tr, context, message, hash_mode, &mu));

  // Invoke the signature generation OTBN app.
  HARDENED_TRY_WIPE_DMEM(
      mldsa87_sign_internal_start(private_key, &mu, sign_mode));

  // Check the buffers again before exiting.
  HARDENED_TRY(check_blinded_key(private_key));
  HARDENED_TRY(check_byte_buf(context, kOtcryptoMldsa87CtxMaxBytes));
  HARDENED_TRY(check_byte_buf(message, kOtcryptoMldsa87MsgMaxBytes));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mldsa87_sign_async_finalize(
    otcrypto_word32_buf_t *signature) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(
      mldsa87_sign_internal_finalize(signature, kMldsa87SingleSign));

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_mldsa87_double_sign_async_finalize(
    otcrypto_word32_buf_t *signature) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (signature == NULL || signature->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY_WIPE_DMEM(
      mldsa87_sign_internal_finalize(signature, kMldsa87DoubleSign));

  return otcrypto_eval_exit(OTCRYPTO_OK);
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

  HARDENED_TRY_WIPE_DMEM(
      mldsa87_verify_internal_finalize(signature, verification_result));

  return otcrypto_eval_exit(OTCRYPTO_OK);
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
