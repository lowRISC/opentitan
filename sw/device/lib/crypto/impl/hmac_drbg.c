// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hmac_drbg.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'd', 'r')

/**
 * Internal HMAC-DRBG context representation.
 */
typedef struct hmac_drbg_ctx {
  /**
   * Masked keyblob for `K`, owned by value so the context contains no pointers.
   */
  uint32_t k_keyblob[2 * kHmacMaxDigestWords];
  /**
   * Checksum of the blinded `K` key.
   */
  uint32_t k_checksum;
  /**
   * Internal `V` state value.
   */
  uint32_t v[kHmacMaxDigestWords];
  /**
   * Current reseed counter.
   */
  uint32_t reseed_counter;
  /**
   * Reseed interval in generate calls.
   */
  uint32_t reseed_interval;
  /**
   * Whether this context has been initialized.
   */
  hardened_bool_t initialized;
  /**
   * Whether automatic reseeding is enabled.
   */
  hardened_bool_t auto_reseed;
  /**
   * Underlying SHA-2 hash mode.
   */
  otcrypto_hash_mode_t hash_mode;
} __attribute__((aligned(sizeof(uint32_t)))) hmac_drbg_ctx_t;

static_assert(sizeof(otcrypto_hmac_drbg_context_t) == sizeof(hmac_drbg_ctx_t),
              "Size of `otcrypto_hmac_drbg_context_t` must match "
              "`hmac_drbg_ctx_t`.");
static_assert(sizeof(hmac_drbg_ctx_t) % sizeof(uint32_t) == 0,
              "Size of `hmac_drbg_ctx_t` must be a multiple of the word size "
              "for use with `hardened_memcpy`.");
static_assert(alignof(hmac_drbg_ctx_t) >= alignof(uint32_t),
              "Internal HMAC-DRBG context object must be word-aligned for use "
              "with `hardened_memcpy`.");

enum {
  kHmacDrbgCtxNumWords = sizeof(hmac_drbg_ctx_t) / sizeof(uint32_t),
};

static const uint32_t kZeroDigest[kHmacMaxDigestWords] = {0};

/**
 * Save an HMAC-DRBG context.
 *
 * @param internal_ctx Internal context object to save.
 * @param[out] api_ctx Resulting API-facing context object.
 * @return Result of the operation.
 */
static inline status_t hmac_drbg_context_save(
    const hmac_drbg_ctx_t *internal_ctx,
    otcrypto_hmac_drbg_context_t *api_ctx) {
  return hardened_memcpy(api_ctx->data, (const uint32_t *)internal_ctx,
                         kHmacDrbgCtxNumWords);
}

/**
 * Restore an HMAC-DRBG context.
 *
 * @param api_ctx API-facing context object to restore from.
 * @param[out] internal_ctx Resulting internal context object.
 * @return Result of the operation.
 */
static inline status_t hmac_drbg_context_restore(
    const otcrypto_hmac_drbg_context_t *api_ctx,
    hmac_drbg_ctx_t *internal_ctx) {
  return hardened_memcpy((uint32_t *)internal_ctx, api_ctx->data,
                         kHmacDrbgCtxNumWords);
}

/**
 * Infer the HMAC key mode and digest length in 32-bit words from the SHA-2 hash
 * mode.
 *
 * @param hash_mode SHA-2 hash mode.
 * @param[out] key_mode Corresponding HMAC key mode.
 * @param[out] digest_words Digest length in 32-bit words.
 * @return OK or error.
 */
static status_t hmac_mode_and_digest_words(otcrypto_hash_mode_t hash_mode,
                                           otcrypto_key_mode_t *key_mode,
                                           size_t *digest_words) {
  *key_mode = (otcrypto_key_mode_t)0;
  *digest_words = 0;
  otcrypto_hash_mode_t mode_used = launder32(0);
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
      *key_mode = kOtcryptoKeyModeHmacSha256;
      *digest_words = kHmacSha256DigestWords;
      mode_used = launder32(mode_used) | kOtcryptoHashModeSha256;
      break;
    case kOtcryptoHashModeSha384:
      *key_mode = kOtcryptoKeyModeHmacSha384;
      *digest_words = kHmacSha384DigestWords;
      mode_used = launder32(mode_used) | kOtcryptoHashModeSha384;
      break;
    case kOtcryptoHashModeSha512:
      *key_mode = kOtcryptoKeyModeHmacSha512;
      *digest_words = kHmacSha512DigestWords;
      mode_used = launder32(mode_used) | kOtcryptoHashModeSha512;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(mode_used), hash_mode);
  HARDENED_CHECK_NE(*digest_words, 0);
  return OTCRYPTO_OK;
}

/**
 * Reconstruct an ephemeral `otcrypto_blinded_key_t` view from the by-value key
 * shares stored inside an `hmac_drbg_ctx_t`.
 *
 * @param ctx Internal HMAC-DRBG context.
 * @param key_mode HMAC key mode.
 * @param digest_words Digest length in 32-bit words.
 * @return Constructed `otcrypto_blinded_key_t` referencing `ctx->k_keyblob`.
 */
static inline otcrypto_blinded_key_t hmac_drbg_context_key(
    hmac_drbg_ctx_t *ctx, otcrypto_key_mode_t key_mode, size_t digest_words) {
  otcrypto_key_config_t k_config = {
      .version = otcrypto_lib_version(),
      .key_mode = key_mode,
      .key_length = digest_words * sizeof(uint32_t),
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  return (otcrypto_blinded_key_t){
      .config = k_config,
      .keyblob_length = keyblob_num_words(k_config) * sizeof(uint32_t),
      .keyblob = ctx->k_keyblob,
      .checksum = ctx->k_checksum,
  };
}

/**
 * Mask an unmasked `K` value into `ctx->k_keyblob` and update
 * `ctx->k_checksum`.
 *
 * @param unmasked_k Unmasked `K` words (`digest_words` words).
 * @param key_mode HMAC key mode.
 * @param digest_words Digest length in 32-bit words.
 * @param[in,out] ctx Internal HMAC-DRBG context.
 * @return OK or error.
 */
static status_t hmac_drbg_set_k(const uint32_t *unmasked_k,
                                otcrypto_key_mode_t key_mode,
                                size_t digest_words, hmac_drbg_ctx_t *ctx) {
  otcrypto_blinded_key_t k_key =
      hmac_drbg_context_key(ctx, key_mode, digest_words);
  uint32_t k_mask[kHmacMaxDigestWords];
  HARDENED_TRY(hardened_memshred(k_mask, digest_words));
  HARDENED_TRY(keyblob_from_key_and_mask(unmasked_k, k_mask, k_key.config,
                                         ctx->k_keyblob));
  ctx->k_checksum = otcrypto_integrity_blinded_checksum(&k_key);
  return OTCRYPTO_OK;
}

/**
 * Update `V = HMAC(K, V)`.
 *
 * @param ctx Internal HMAC-DRBG context.
 * @return OK or error.
 */
static status_t update_v(hmac_drbg_ctx_t *ctx) {
  otcrypto_key_mode_t key_mode;
  size_t digest_words = 0;
  HARDENED_TRY(
      hmac_mode_and_digest_words(ctx->hash_mode, &key_mode, &digest_words));

  otcrypto_blinded_key_t k_key =
      hmac_drbg_context_key(ctx, key_mode, digest_words);
  otcrypto_const_byte_buf_t v_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const unsigned char *)ctx->v,
      digest_words * sizeof(uint32_t));
  uint32_t new_v[kHmacMaxDigestWords];
  otcrypto_word32_buf_t v_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, new_v, digest_words);

  HARDENED_TRY(otcrypto_hmac(&k_key, &v_in, &v_out));

  HARDENED_TRY(hardened_memcpy(ctx->v, new_v, digest_words));
  HARDENED_CHECK_EQ(hardened_memeq(ctx->v, new_v, digest_words),
                    kHardenedBoolTrue);
  HARDENED_TRY(hardened_memshred(new_v, digest_words));

  // Fault countermeasure: ensure the updated V is not all zero.
  HARDENED_CHECK_EQ(hardened_memeq(ctx->v, kZeroDigest, digest_words),
                    kHardenedBoolFalse);

  return OTCRYPTO_OK;
}

/**
 * Perform one round of `K = HMAC(K, V || tag || data0 || data1 || data2)`
 * followed by `V = HMAC(K, V)`.
 *
 * @param ctx Internal HMAC-DRBG context.
 * @param tag Single-byte separator (0x00 or 0x01).
 * @param data0 First input buffer (e.g. entropy; may have length 0).
 * @param data1 Second input buffer (e.g. nonce; may have length 0).
 * @param data2 Third input buffer (e.g. perso/additional input; may have
 * length 0).
 * @return OK or error.
 */
static status_t update_kv(hmac_drbg_ctx_t *ctx, uint8_t tag,
                          const otcrypto_const_byte_buf_t *data0,
                          const otcrypto_const_byte_buf_t *data1,
                          const otcrypto_const_byte_buf_t *data2) {
  otcrypto_key_mode_t key_mode;
  size_t digest_words = 0;
  HARDENED_TRY(
      hmac_mode_and_digest_words(ctx->hash_mode, &key_mode, &digest_words));

  otcrypto_blinded_key_t k_key =
      hmac_drbg_context_key(ctx, key_mode, digest_words);
  otcrypto_hmac_context_t hmac_ctx;
  HARDENED_TRY(otcrypto_hmac_init(&hmac_ctx, &k_key));

  otcrypto_const_byte_buf_t v_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const unsigned char *)ctx->v,
      digest_words * sizeof(uint32_t));
  HARDENED_TRY(otcrypto_hmac_update(&hmac_ctx, &v_buf));

  otcrypto_const_byte_buf_t tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, &tag, sizeof(tag));
  HARDENED_TRY(otcrypto_hmac_update(&hmac_ctx, &tag_buf));

  if (launder32(data0->len) != 0) {
    HARDENED_TRY(otcrypto_hmac_update(&hmac_ctx, data0));
  } else {
    HARDENED_CHECK_EQ(data0->len, 0);
  }
  if (launder32(data1->len) != 0) {
    HARDENED_TRY(otcrypto_hmac_update(&hmac_ctx, data1));
  } else {
    HARDENED_CHECK_EQ(data1->len, 0);
  }
  if (launder32(data2->len) != 0) {
    HARDENED_TRY(otcrypto_hmac_update(&hmac_ctx, data2));
  } else {
    HARDENED_CHECK_EQ(data2->len, 0);
  }

  uint32_t new_k[kHmacMaxDigestWords];
  otcrypto_word32_buf_t k_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, new_k, digest_words);
  HARDENED_TRY(otcrypto_hmac_final(&hmac_ctx, &k_out));

  // Fault countermeasure: ensure the updated K is not all zero.
  HARDENED_CHECK_EQ(hardened_memeq(new_k, kZeroDigest, digest_words),
                    kHardenedBoolFalse);

  HARDENED_TRY(hmac_drbg_set_k(new_k, key_mode, digest_words, ctx));
  HARDENED_TRY(hardened_memshred(new_k, digest_words));

  return update_v(ctx);
}

/**
 * Perform the NIST SP 800-90Ar1 Section 10.1.2.2 `HMAC_DRBG_Update` operation.
 *
 * @param ctx Internal HMAC-DRBG context.
 * @param data0 First input buffer (e.g. entropy; may have length 0).
 * @param data1 Second input buffer (e.g. nonce; may have length 0).
 * @param data2 Third input buffer (e.g. perso/additional input; may have
 * length 0).
 * @return OK or error.
 */
static status_t hmac_drbg_update(hmac_drbg_ctx_t *ctx,
                                 const otcrypto_const_byte_buf_t *data0,
                                 const otcrypto_const_byte_buf_t *data1,
                                 const otcrypto_const_byte_buf_t *data2) {
  HARDENED_TRY(update_kv(ctx, 0x00, data0, data1, data2));

  size_t provided_data_len = data0->len | data1->len | data2->len;
  if (launder32(provided_data_len) == 0) {
    HARDENED_CHECK_EQ(provided_data_len, 0);
    return OTCRYPTO_OK;
  }
  return update_kv(ctx, 0x01, data0, data1, data2);
}

otcrypto_status_t otcrypto_hmac_drbg_init(
    otcrypto_hmac_drbg_context_t *ctx, const otcrypto_const_byte_buf_t *entropy,
    const otcrypto_const_byte_buf_t *nonce,
    const otcrypto_const_byte_buf_t *perso_string, uint32_t reseed_interval,
    otcrypto_hash_mode_t hash_mode) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_DRBG_INIT);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || entropy == NULL || entropy->data == NULL ||
      nonce == NULL || nonce->data == NULL || perso_string == NULL ||
      (perso_string->data == NULL && perso_string->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(entropy->len) == 0 || launder32(nonce->len) == 0 ||
      launder32(reseed_interval) == 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(entropy->len, 0);
  HARDENED_CHECK_NE(nonce->len, 0);
  HARDENED_CHECK_NE(reseed_interval, 0);
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(entropy));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(nonce));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(perso_string));

  otcrypto_key_mode_t key_mode;
  size_t digest_words = 0;
  HARDENED_TRY(hmac_mode_and_digest_words(hash_mode, &key_mode, &digest_words));

  HARDENED_TRY(hardened_memshred(ctx->data, ARRAYSIZE(ctx->data)));

  hmac_drbg_ctx_t internal_ctx;
  HARDENED_TRY(
      hardened_memshred((uint32_t *)&internal_ctx, kHmacDrbgCtxNumWords));

  internal_ctx.reseed_counter = 1;
  internal_ctx.hash_mode = hash_mode;
  // V = 0x01 0x01 0x01 ... 0x01
  memset(internal_ctx.v, 0x01, digest_words * sizeof(uint32_t));
  // K = 0x00 0x00 0x00 ... 0x00 (masked into k_keyblob)
  HARDENED_TRY(
      hmac_drbg_set_k(kZeroDigest, key_mode, digest_words, &internal_ctx));

  HARDENED_TRY(hmac_drbg_update(&internal_ctx, entropy, nonce, perso_string));

  internal_ctx.initialized = kHardenedBoolTrue;
  internal_ctx.auto_reseed = kHardenedBoolFalse;
  internal_ctx.reseed_interval = reseed_interval;

  HARDENED_TRY(hmac_drbg_context_save(&internal_ctx, ctx));
  HARDENED_TRY(
      hardened_memshred((uint32_t *)&internal_ctx, kHmacDrbgCtxNumWords));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_hmac_drbg_deinit(otcrypto_hmac_drbg_context_t *ctx) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_DRBG_DEINIT);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  HARDENED_TRY(hardened_memshred(ctx->data, ARRAYSIZE(ctx->data)));
  hmac_drbg_ctx_t *internal_ctx = (hmac_drbg_ctx_t *)ctx->data;
  internal_ctx->initialized = kHardenedBoolFalse;

  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_hmac_drbg_reseed(
    otcrypto_hmac_drbg_context_t *ctx, const otcrypto_const_byte_buf_t *entropy,
    const otcrypto_const_byte_buf_t *additional_input) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_DRBG_RESEED);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || entropy == NULL || entropy->data == NULL ||
      additional_input == NULL ||
      (additional_input->data == NULL && additional_input->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(entropy->len) == 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_NE(entropy->len, 0);
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(entropy));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(additional_input));

  hmac_drbg_ctx_t internal_ctx;
  HARDENED_TRY(hmac_drbg_context_restore(ctx, &internal_ctx));
  if (launder32(internal_ctx.initialized) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(internal_ctx.initialized, kHardenedBoolTrue);

  otcrypto_const_byte_buf_t empty =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  HARDENED_TRY(
      hmac_drbg_update(&internal_ctx, entropy, &empty, additional_input));
  internal_ctx.reseed_counter = 1;

  HARDENED_TRY(hmac_drbg_context_save(&internal_ctx, ctx));
  HARDENED_TRY(
      hardened_memshred((uint32_t *)&internal_ctx, kHmacDrbgCtxNumWords));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_hmac_drbg_set_auto_reseed(
    otcrypto_hmac_drbg_context_t *ctx, hardened_bool_t enabled) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_DRBG_SET_AUTO_RESEED);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hmac_drbg_ctx_t *internal_ctx = (hmac_drbg_ctx_t *)ctx->data;
  if (launder32(internal_ctx->initialized) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(internal_ctx->initialized, kHardenedBoolTrue);

  if (launder32(enabled) != kHardenedBoolTrue &&
      launder32(enabled) != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  internal_ctx->auto_reseed = enabled;
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_hmac_drbg_generate(
    otcrypto_hmac_drbg_context_t *ctx,
    const otcrypto_const_byte_buf_t *additional_input,
    otcrypto_byte_buf_t *drbg_output) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_DRBG_GENERATE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || additional_input == NULL || drbg_output == NULL ||
      (additional_input->data == NULL && additional_input->len != 0) ||
      (drbg_output->data == NULL && drbg_output->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(additional_input));
  HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(drbg_output));

  if (launder32(drbg_output->len) > kOtcryptoHmacDrbgMaxOutputBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_LE(drbg_output->len, kOtcryptoHmacDrbgMaxOutputBytes);

  hmac_drbg_ctx_t internal_ctx;
  HARDENED_TRY(hmac_drbg_context_restore(ctx, &internal_ctx));
  if (launder32(internal_ctx.initialized) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(internal_ctx.initialized, kHardenedBoolTrue);

  otcrypto_key_mode_t key_mode;
  size_t digest_words = 0;
  HARDENED_TRY(hmac_mode_and_digest_words(internal_ctx.hash_mode, &key_mode,
                                          &digest_words));
  size_t digest_bytelen = digest_words * sizeof(uint32_t);

  otcrypto_const_byte_buf_t empty =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  if (launder32(internal_ctx.reseed_counter) >
      launder32(internal_ctx.reseed_interval)) {
    if (launder32(internal_ctx.auto_reseed) == kHardenedBoolFalse) {
      HARDENED_TRY(
          hardened_memshred((uint32_t *)&internal_ctx, kHmacDrbgCtxNumWords));
      return otcrypto_eval_exit(OTCRYPTO_RECOV_ERR);
    }
    HARDENED_CHECK_EQ(internal_ctx.auto_reseed, kHardenedBoolTrue);
    uint32_t seed[kHmacMaxDigestWords];
    HARDENED_TRY(hardened_memshred(seed, ARRAYSIZE(seed)));
    otcrypto_word32_buf_t seed_words =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, seed, ARRAYSIZE(seed));
    HARDENED_TRY(otcrypto_drbg_instantiate(&empty));
    HARDENED_TRY(otcrypto_drbg_generate(&empty, &seed_words));
    otcrypto_const_byte_buf_t seed_bytes = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, (const unsigned char *)seed, sizeof(seed));
    // Per NIST SP 800-90Ar1 Section 9.3.1 Steps 7.1-7.3, absorb
    // `additional_input` during the reseed and replace it with the empty
    // string for the subsequent generate steps.
    HARDENED_TRY(
        hmac_drbg_update(&internal_ctx, &seed_bytes, &empty, additional_input));
    internal_ctx.reseed_counter = 1;
    additional_input = &empty;
    HARDENED_TRY(hardened_memshred(seed, ARRAYSIZE(seed)));
  } else {
    HARDENED_CHECK_LE(internal_ctx.reseed_counter,
                      internal_ctx.reseed_interval);
  }

  if (launder32(additional_input->len) != 0) {
    HARDENED_TRY(
        hmac_drbg_update(&internal_ctx, &empty, &empty, additional_input));
  } else {
    HARDENED_CHECK_EQ(additional_input->len, 0);
  }

  size_t num_iterations = ceil_div(drbg_output->len, digest_bytelen);
  size_t bytes_written = 0;
  size_t i = 0;
  for (; launder32(i) < num_iterations; i++) {
    HARDENED_TRY(update_v(&internal_ctx));
    size_t bytes_to_copy = digest_bytelen;
    if (bytes_written + digest_bytelen > drbg_output->len) {
      bytes_to_copy = drbg_output->len - bytes_written;
    }
    HARDENED_TRY(randomized_bytecopy(drbg_output->data + bytes_written,
                                     internal_ctx.v, bytes_to_copy));
    HARDENED_CHECK_EQ(
        consttime_memeq_byte(internal_ctx.v, drbg_output->data + bytes_written,
                             bytes_to_copy),
        kHardenedBoolTrue);
    bytes_written += bytes_to_copy;
  }
  HARDENED_CHECK_EQ(i, num_iterations);
  HARDENED_CHECK_EQ(bytes_written, drbg_output->len);

  HARDENED_TRY(
      hmac_drbg_update(&internal_ctx, &empty, &empty, additional_input));
  internal_ctx.reseed_counter++;

  HARDENED_TRY(hmac_drbg_context_save(&internal_ctx, ctx));
  HARDENED_TRY(
      hardened_memshred((uint32_t *)&internal_ctx, kHmacDrbgCtxNumWords));
  return otcrypto_eval_exit(OTCRYPTO_OK);
}
