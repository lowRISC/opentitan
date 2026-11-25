// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/sha2.h"

#include <stdbool.h>

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha1.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', 'h', '2')

// Ensure that the hash context is large enough for HMAC driver struct.
static_assert(
    sizeof(otcrypto_sha2_context_t) == sizeof(hmac_ctx_t),
    "`otcrypto_sha2_context_t` must be the same size as `hmac_ctx_t`.");

// Ensure that `otcrypto_hash_context_t` can hold a mode word plus either a
// SHA-2 or SHA-1 streaming context.
static_assert(sizeof(otcrypto_hash_context_t) >=
                  sizeof(uint32_t) + sizeof(otcrypto_sha2_context_t),
              "`otcrypto_hash_context_t` must hold a mode word plus "
              "`otcrypto_sha2_context_t`.");
static_assert(sizeof(otcrypto_hash_context_t) >=
                  sizeof(uint32_t) + sizeof(otcrypto_sha1_context_t),
              "`otcrypto_hash_context_t` must hold a mode word plus "
              "`otcrypto_sha1_context_t`.");

otcrypto_status_t otcrypto_sha2_256(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA2_256);
  OTCRYPTO_HEALTH_CHECK(kTestHashSha256Bit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(digest->len) != kHmacSha256DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kHmacSha256DigestWords);
  digest->mode = kOtcryptoHashModeSha256;

  return otcrypto_eval_exit(hmac_hash_sha256(message, digest->data));
}

otcrypto_status_t otcrypto_sha2_384(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA2_384);
  OTCRYPTO_HEALTH_CHECK(kTestHashSha512Bit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(digest->len) != kHmacSha384DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kHmacSha384DigestWords);
  digest->mode = kOtcryptoHashModeSha384;

  return otcrypto_eval_exit(hmac_hash_sha384(message, digest->data));
}

otcrypto_status_t otcrypto_sha2_512(const otcrypto_const_byte_buf_t *message,
                                    otcrypto_hash_digest_t *digest) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA2_512);
  OTCRYPTO_HEALTH_CHECK(kTestHashSha512Bit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(digest->len) != kHmacSha512DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kHmacSha512DigestWords);
  digest->mode = kOtcryptoHashModeSha512;

  return otcrypto_eval_exit(hmac_hash_sha512(message, digest->data));
}

otcrypto_status_t otcrypto_sha2_init(otcrypto_hash_mode_t hash_mode,
                                     otcrypto_sha2_context_t *ctx) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA2_INIT);
  OTCRYPTO_HEALTH_CHECK(hash_mode == kOtcryptoHashModeSha256
                            ? kTestHashSha256Bit
                            : kTestHashSha512Bit);
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hmac_ctx_t hmac_ctx = {0};
  otcrypto_hash_mode_t hash_mode_used = launder32(0);
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256: {
      hmac_hash_sha256_init(&hmac_ctx);
      hash_mode_used = launder32(hash_mode_used) | kOtcryptoHashModeSha256;
      break;
    }
    case kOtcryptoHashModeSha384: {
      hmac_hash_sha384_init(&hmac_ctx);
      hash_mode_used = launder32(hash_mode_used) | kOtcryptoHashModeSha384;
      break;
    }
    case kOtcryptoHashModeSha512: {
      hmac_hash_sha512_init(&hmac_ctx);
      hash_mode_used = launder32(hash_mode_used) | kOtcryptoHashModeSha512;
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(hash_mode_used), hash_mode);

  randomized_bytecopy(ctx->data, &hmac_ctx, sizeof(hmac_ctx));
  HARDENED_CHECK_EQ(
      consttime_memeq_byte(&hmac_ctx, ctx->data, sizeof(hmac_ctx)),
      kHardenedBoolTrue);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

/**
 * Check that the message and digest sizes in a context are safe.
 *
 * Checking that these values are within maximum bounds protects from
 * out-of-bounds writes in the HMAC driver, in case a caller changes the
 * context in between calls.
 *
 * @param ctx HMAC context object.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
static status_t check_lengths(const hmac_ctx_t *hmac_ctx) {
  if (hmac_ctx->msg_block_wordlen == 0 ||
      hmac_ctx->msg_block_wordlen > kHmacMaxBlockWords ||
      hmac_ctx->digest_wordlen > kHmacMaxDigestWords ||
      hmac_ctx->partial_block_bytelen >=
          hmac_ctx->msg_block_wordlen * sizeof(uint32_t) ||
      hmac_ctx->key.key_len > kHmacMaxBlockWords) {
    // COVERAGE (MISSING) We do not cover badly encoded contexts.
    return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_sha2_update(
    otcrypto_sha2_context_t *ctx, const otcrypto_const_byte_buf_t *message) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA2_UPDATE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || message == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Return early if the update size is 0.
  if (launderw(message->len) == 0) {
    HARDENED_CHECK_EQ(kHardenedBoolTrue, OTCRYPTO_CHECK_BUF(message));
    HARDENED_CHECK_EQ(message->len, 0);
    return otcrypto_eval_exit(OTCRYPTO_OK);
  }

#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (message->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hmac_ctx_t *hmac_ctx = (hmac_ctx_t *)ctx->data;
  HARDENED_TRY(check_lengths(hmac_ctx));
  return otcrypto_eval_exit(hmac_update(hmac_ctx, message));
}

otcrypto_status_t otcrypto_sha2_final(otcrypto_sha2_context_t *ctx,
                                      otcrypto_hash_digest_t *digest) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA2_FINAL);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hmac_ctx_t *hmac_ctx = (hmac_ctx_t *)ctx->data;
  HARDENED_TRY(check_lengths(hmac_ctx));

  if (launderw(digest->len) != launderw(hmac_ctx->digest_wordlen)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, hmac_ctx->digest_wordlen);

  // Infer the mode from the digest length.
  size_t len_used = launder32(0);
  switch (launder32(digest->len)) {
    case kHmacSha256DigestWords:
      digest->mode = kOtcryptoHashModeSha256;
      len_used = launder32(len_used) | kHmacSha256DigestWords;
      break;
    case kHmacSha384DigestWords:
      digest->mode = kOtcryptoHashModeSha384;
      len_used = launder32(len_used) | kHmacSha384DigestWords;
      break;
    case kHmacSha512DigestWords:
      digest->mode = kOtcryptoHashModeSha512;
      len_used = launder32(len_used) | kHmacSha512DigestWords;
      break;
    default:
      // COVERAGE (MISSING) We do not cover bad digest lengths.
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(len_used), digest->len);

  otcrypto_word32_buf_t digest_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, digest->data, digest->len);

  return otcrypto_eval_exit(hmac_final(hmac_ctx, &digest_buf));
}

otcrypto_status_t otcrypto_hash_init(otcrypto_hash_context_t *ctx,
                                     otcrypto_hash_mode_t hash_mode) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
    case kOtcryptoHashModeSha384:
    case kOtcryptoHashModeSha512: {
      ctx->data[0] = (uint32_t)hash_mode;
      otcrypto_sha2_context_t *sha2_ctx =
          (otcrypto_sha2_context_t *)&ctx->data[1];
      return otcrypto_sha2_init(hash_mode, sha2_ctx);
    }
    case kOtcryptoHashModeSha1: {
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha1);
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      ctx->data[0] = (uint32_t)kOtcryptoHashModeSha1;
      otcrypto_sha1_context_t *sha1_ctx =
          (otcrypto_sha1_context_t *)&ctx->data[1];
      return otcrypto_sha1_init(sha1_ctx);
    }
    default:
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      return OTCRYPTO_BAD_ARGS;
  }
}

otcrypto_status_t otcrypto_hash_update(
    otcrypto_hash_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || input_message == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  otcrypto_hash_mode_t hash_mode = (otcrypto_hash_mode_t)ctx->data[0];
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
    case kOtcryptoHashModeSha384:
    case kOtcryptoHashModeSha512: {
      OTCRYPTO_HEALTH_CHECK(hash_mode == kOtcryptoHashModeSha256
                                ? kTestHashSha256Bit
                                : kTestHashSha512Bit);
      otcrypto_sha2_context_t *sha2_ctx =
          (otcrypto_sha2_context_t *)&ctx->data[1];
      return otcrypto_sha2_update(sha2_ctx, input_message);
    }
    case kOtcryptoHashModeSha1: {
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha1);
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      otcrypto_sha1_context_t *sha1_ctx =
          (otcrypto_sha1_context_t *)&ctx->data[1];
      return otcrypto_sha1_update(sha1_ctx, input_message);
    }
    default:
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      return OTCRYPTO_BAD_ARGS;
  }
}

otcrypto_status_t otcrypto_hash_final(otcrypto_hash_context_t *ctx,
                                      otcrypto_hash_digest_t *digest) {
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || digest == NULL || digest->data == NULL) {
    OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  otcrypto_hash_mode_t hash_mode = (otcrypto_hash_mode_t)ctx->data[0];
  status_t status = OTCRYPTO_BAD_ARGS;
  switch (launder32(hash_mode)) {
    case kOtcryptoHashModeSha256:
    case kOtcryptoHashModeSha384:
    case kOtcryptoHashModeSha512: {
      OTCRYPTO_HEALTH_CHECK(hash_mode == kOtcryptoHashModeSha256
                                ? kTestHashSha256Bit
                                : kTestHashSha512Bit);
      otcrypto_sha2_context_t *sha2_ctx =
          (otcrypto_sha2_context_t *)&ctx->data[1];
      status = otcrypto_sha2_final(sha2_ctx, digest);
      break;
    }
    case kOtcryptoHashModeSha1: {
      HARDENED_CHECK_EQ(hash_mode, kOtcryptoHashModeSha1);
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      otcrypto_sha1_context_t *sha1_ctx =
          (otcrypto_sha1_context_t *)&ctx->data[1];
      status = otcrypto_sha1_final(sha1_ctx, digest);
      break;
    }
    default:
      OTCRYPTO_CMVP_OVERRIDE_NOT_APPROVED();
      return OTCRYPTO_BAD_ARGS;
  }

  hardened_memshred(ctx->data, ARRAYSIZE(ctx->data));
  return status;
}
