// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hash.h"

#include <stdbool.h>

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'a', 's')

// Check that internal and publicly exposed digest values match each other.
static_assert(kSha256DigestBits == kHmacSha256DigestBits &&
                  kSha256DigestBytes == kHmacSha256DigestBytes &&
                  kSha256DigestWords == kHmacSha256DigestWords,
              "Exposed and driver-level SHA-256 digest size mismatch.");
static_assert(kSha384DigestBits == kHmacSha384DigestBits &&
                  kSha384DigestBytes == kHmacSha384DigestBytes &&
                  kSha384DigestWords == kHmacSha384DigestWords,
              "Exposed and driver-level SHA-384 digest size mismatch.");
static_assert(kSha512DigestBits == kHmacSha512DigestBits &&
                  kSha512DigestBytes == kHmacSha512DigestBytes &&
                  kSha512DigestWords == kHmacSha512DigestWords,
              "Exposed and driver-level SHA-512 digest size mismatch.");

// Ensure that the hash context is large enough for HMAC driver struct.
static_assert(
    sizeof(otcrypto_hash_context_t) >= sizeof(hmac_ctx_t),
    "`otcrypto_hash_context_t` must be big enough to hold `hmac_ctx_t`.");

// Ensure that HMAC driver struct is suitable for `hardened_memcpy()`.
static_assert(sizeof(hmac_ctx_t) % sizeof(uint32_t) == 0,
              "Size of `hmac_ctx_t` must be a multiple of the word size for "
              "`hardened_memcpy()`");

/**
 * Save the internal HMAC driver context to a generic hash context.
 *
 * @param[out] ctx Generic hash context to copy to.
 * @param hmac_ctx The internal context object from HMAC driver.
 */
static void hmac_ctx_save(otcrypto_hash_context_t *restrict ctx,
                          const hmac_ctx_t *restrict hmac_ctx) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy(ctx->data, (uint32_t *)hmac_ctx,
                  sizeof(hmac_ctx_t) / sizeof(uint32_t));
}

/**
 * Restore an internal HMAC driver context from a generic hash context.
 *
 * @param ctx Generic hash context to restore from.
 * @param[out] hmac_ctx Destination HMAC driver context object.
 */
static void hmac_ctx_restore(const otcrypto_hash_context_t *restrict ctx,
                             hmac_ctx_t *restrict hmac_ctx) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy((uint32_t *)hmac_ctx, ctx->data,
                  sizeof(hmac_ctx_t) / sizeof(uint32_t));
}

/**
 * Checks that the `mode` and `len` fields of the digest match.
 *
 * Ignores the digest `data` field; safe to use on uninitialized digests.
 *
 * @param digest Digest struct with `mode` and `len` set.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
static status_t check_digest_len(otcrypto_hash_digest_t digest) {
  switch (launder32(digest.mode)) {
    case kOtcryptoHashModeSha3_224:
      if (launder32(digest.len) == (224 / 32)) {
        HARDENED_CHECK_EQ(digest.len * sizeof(uint32_t) * 8, 224);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    case kOtcryptoHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoHashModeSha3_256:
      if (launder32(digest.len) == (256 / 32)) {
        HARDENED_CHECK_EQ(digest.len * sizeof(uint32_t) * 8, 256);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    case kOtcryptoHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoHashModeSha3_384:
      if (launder32(digest.len) == (384 / 32)) {
        HARDENED_CHECK_EQ(digest.len * sizeof(uint32_t) * 8, 384);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    case kOtcryptoHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kOtcryptoHashModeSha3_512:
      if (launder32(digest.len) == (512 / 32)) {
        HARDENED_CHECK_EQ(digest.len * sizeof(uint32_t) * 8, 512);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_hash(otcrypto_const_byte_buf_t input_message,
                                otcrypto_hash_digest_t digest) {
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (digest.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that digest length and mode match.
  HARDENED_TRY(check_digest_len(digest));

  switch (digest.mode) {
    case kOtcryptoHashModeSha3_224:
      return kmac_sha3_224(input_message.data, input_message.len, digest.data);
    case kOtcryptoHashModeSha3_256:
      return kmac_sha3_256(input_message.data, input_message.len, digest.data);
    case kOtcryptoHashModeSha3_384:
      return kmac_sha3_384(input_message.data, input_message.len, digest.data);
    case kOtcryptoHashModeSha3_512:
      return kmac_sha3_512(input_message.data, input_message.len, digest.data);
    case kOtcryptoHashModeSha256:
      return hmac(kHmacModeSha256, /*key=*/NULL, /*key_wordlen=*/0,
                  input_message.data, input_message.len, digest.data,
                  digest.len);
      break;
    case kOtcryptoHashModeSha384:
      return hmac(kHmacModeSha384, /*key=*/NULL, /*key_wordlen=*/0,
                  input_message.data, input_message.len, digest.data,
                  digest.len);
      break;
    case kOtcryptoHashModeSha512:
      return hmac(kHmacModeSha512, /*key=*/NULL, /*key_wordlen=*/0,
                  input_message.data, input_message.len, digest.data,
                  digest.len);
      break;
    default:
      // Invalid hash mode.
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_xof_shake(otcrypto_const_byte_buf_t input_message,
                                     otcrypto_hash_digest_t digest) {
  switch (digest.mode) {
    case kOtcryptoHashXofModeShake128:
      return kmac_shake_128(input_message.data, input_message.len, digest.data,
                            digest.len);
    case kOtcryptoHashXofModeShake256:
      return kmac_shake_256(input_message.data, input_message.len, digest.data,
                            digest.len);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_xof_cshake(
    otcrypto_const_byte_buf_t input_message,
    otcrypto_const_byte_buf_t function_name_string,
    otcrypto_const_byte_buf_t customization_string,
    otcrypto_hash_digest_t digest) {
  // According to NIST SP 800-185 Section 3.2, cSHAKE call should use SHAKE, if
  // both `customization_string` and `function_name_string` are empty string
  if (customization_string.len == 0 && function_name_string.len == 0) {
    switch (digest.mode) {
      case kOtcryptoHashXofModeCshake128:
        return kmac_shake_128(input_message.data, input_message.len,
                              digest.data, digest.len);
      case kOtcryptoHashXofModeCshake256:
        return kmac_shake_256(input_message.data, input_message.len,
                              digest.data, digest.len);
      default:
        return OTCRYPTO_BAD_ARGS;
    }
  }

  switch (digest.mode) {
    case kOtcryptoHashXofModeCshake128:
      return kmac_cshake_128(
          input_message.data, input_message.len, function_name_string.data,
          function_name_string.len, customization_string.data,
          customization_string.len, digest.data, digest.len);
      break;
    case kOtcryptoHashXofModeCshake256:
      return kmac_cshake_256(
          input_message.data, input_message.len, function_name_string.data,
          function_name_string.len, customization_string.data,
          customization_string.len, digest.data, digest.len);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_hash_init(otcrypto_hash_context_t *const ctx,
                                     otcrypto_hash_mode_t hash_mode) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  hmac_ctx_t hmac_ctx;
  switch (hash_mode) {
    case kOtcryptoHashModeSha256: {
      HARDENED_TRY(hmac_init(&hmac_ctx, kHmacModeSha256, /*hmac_key=*/NULL,
                             /*key_wordlen=*/0));
      break;
    }
    case kOtcryptoHashModeSha384: {
      HARDENED_TRY(hmac_init(&hmac_ctx, kHmacModeSha384, /*hmac_key=*/NULL,
                             /*key_wordlen=*/0));
      break;
    }
    case kOtcryptoHashModeSha512: {
      HARDENED_TRY(hmac_init(&hmac_ctx, kHmacModeSha512, /*hmac_key=*/NULL,
                             /*key_wordlen=*/0));
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return OTCRYPTO_BAD_ARGS;
  }

  hmac_ctx_save(ctx, &hmac_ctx);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hash_update(
    otcrypto_hash_context_t *const ctx,
    otcrypto_const_byte_buf_t input_message) {
  if (ctx == NULL || (input_message.data == NULL && input_message.len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  hmac_ctx_t hmac_ctx;
  hmac_ctx_restore(ctx, &hmac_ctx);
  HARDENED_TRY(hmac_update(&hmac_ctx, input_message.data, input_message.len));
  hmac_ctx_save(ctx, &hmac_ctx);
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_hash_final(otcrypto_hash_context_t *const ctx,
                                      otcrypto_hash_digest_t digest) {
  if (ctx == NULL || digest.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that digest length and mode are consistent.
  HARDENED_TRY(check_digest_len(digest));

  hmac_ctx_t hmac_ctx;
  hmac_ctx_restore(ctx, &hmac_ctx);
  HARDENED_TRY(hmac_final(&hmac_ctx, digest.data, digest.len));
  // TODO(#23191): Clear `ctx`.
  hmac_ctx_save(ctx, &hmac_ctx);
  return OTCRYPTO_OK;
}
