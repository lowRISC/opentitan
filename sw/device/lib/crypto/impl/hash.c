// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/hash.h"

#include <stdbool.h>

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/hmac.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/sha2/sha256.h"
#include "sw/device/lib/crypto/impl/sha2/sha512.h"
#include "sw/device/lib/crypto/impl/status.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('h', 'a', 's')

/**
 * Ensure that the hash context is large enough for all SHA2 state structs.
 */
static_assert(sizeof(hash_context_t) >= sizeof(sha256_state_t),
              "hash_context_t must be big enough to hold sha256_state_t");
static_assert(sizeof(hash_context_t) >= sizeof(sha384_state_t),
              "hash_context_t must be big enough to hold sha384_state_t");
static_assert(sizeof(hash_context_t) >= sizeof(sha512_state_t),
              "hash_context_t must be big enough to hold sha512_state_t");
/**
 * Ensure that all SHA2 state structs are suitable for `hardened_memcpy()`.
 */
static_assert(sizeof(sha256_state_t) % sizeof(uint32_t) == 0,
              "Size of sha256_state_t must be a multiple of the word size for "
              "`hardened_memcpy()`");
static_assert(sizeof(sha384_state_t) % sizeof(uint32_t) == 0,
              "Size of sha384_state_t must be a multiple of the word size for "
              "`hardened_memcpy()`");
static_assert(sizeof(sha512_state_t) % sizeof(uint32_t) == 0,
              "Size of sha512_state_t must be a multiple of the word size for "
              "`hardened_memcpy()`");
/**
 * Save a SHA-256 state to a generic hash context.
 *
 * @param[out] ctx Generic hash context to copy to.
 * @param state SHA-256 context object.
 */
static void sha256_state_save(hash_context_t *restrict ctx,
                              const sha256_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy(ctx->data, (uint32_t *)state,
                  sizeof(sha256_state_t) / sizeof(uint32_t));
}

/**
 * Restore a SHA-256 state from a generic hash context.
 *
 * @param ctx Generic hash context to restore from.
 * @param[out] state Destination SHA-256 context object.
 */
static void sha256_state_restore(const hash_context_t *restrict ctx,
                                 sha256_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy((uint32_t *)state, ctx->data,
                  sizeof(sha256_state_t) / sizeof(uint32_t));
}

/**
 * Save a SHA-384 state to a generic hash context.
 *
 * @param[out] ctx Generic hash context to copy to.
 * @param state SHA-384 context object.
 */
static void sha384_state_save(hash_context_t *restrict ctx,
                              const sha384_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy(ctx->data, (uint32_t *)state,
                  sizeof(sha384_state_t) / sizeof(uint32_t));
}

/**
 * Restore a SHA-384 state from a generic hash context.
 *
 * @param ctx Generic hash context to restore from.
 * @param[out] state Destination SHA-384 context object.
 */
static void sha384_state_restore(const hash_context_t *restrict ctx,
                                 sha384_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy((uint32_t *)state, ctx->data,
                  sizeof(sha384_state_t) / sizeof(uint32_t));
}

/**
 * Save a SHA-512 state to a generic hash context.
 *
 * @param[out] ctx Generic hash context to copy to.
 * @param state SHA-512 context object.
 */
static void sha512_state_save(hash_context_t *restrict ctx,
                              const sha512_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy(ctx->data, (uint32_t *)state,
                  sizeof(sha512_state_t) / sizeof(uint32_t));
}

/**
 * Restore a SHA-512 state from a generic hash context.
 *
 * @param ctx Generic hash context to restore from.
 * @param[out] state Destination SHA-512 context object.
 */
static void sha512_state_restore(const hash_context_t *restrict ctx,
                                 sha512_state_t *restrict state) {
  // As per the `hardened_memcpy()` documentation, it is OK to cast to
  // `uint32_t *` here as long as `state` is word-aligned, which it must be
  // because all its fields are.
  hardened_memcpy((uint32_t *)state, ctx->data,
                  sizeof(sha512_state_t) / sizeof(uint32_t));
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
static status_t check_digest_len(hash_digest_t *digest) {
  switch (launder32(digest->mode)) {
    case kHashModeSha3_224:
      if (launder32(digest->len) == (224 / 32)) {
        HARDENED_CHECK_EQ(digest->len * sizeof(uint32_t) * 8, 224);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    case kHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_256:
      if (launder32(digest->len) == (256 / 32)) {
        HARDENED_CHECK_EQ(digest->len * sizeof(uint32_t) * 8, 256);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    case kHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_384:
      if (launder32(digest->len) == (384 / 32)) {
        HARDENED_CHECK_EQ(digest->len * sizeof(uint32_t) * 8, 384);
        return OTCRYPTO_OK;
      }
      return OTCRYPTO_BAD_ARGS;
    case kHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_512:
      if (launder32(digest->len) == (512 / 32)) {
        HARDENED_CHECK_EQ(digest->len * sizeof(uint32_t) * 8, 512);
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

/**
 * Compute SHA256 using the HMAC hardware block.
 *
 * @param message Message to hash.
 * @param[out] digest Output digest.
 */
OT_WARN_UNUSED_RESULT
static status_t hmac_sha256(crypto_const_byte_buf_t message,
                            hash_digest_t *digest) {
  HARDENED_CHECK_EQ(digest->len, kHmacDigestNumWords);
  HARDENED_CHECK_EQ(digest->mode, kHashModeSha256);

  // Initialize the hardware.
  hmac_sha_init();

  // Pass the message and check the length.
  hmac_update(message.data, message.len);

  // Retrieve the digest and copy it to the destination buffer.
  hmac_digest_t hmac_digest;
  hmac_final(&hmac_digest);
  hardened_memcpy(digest->data, hmac_digest.digest, kHmacDigestNumWords);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hash(crypto_const_byte_buf_t input_message,
                              hash_digest_t *digest) {
  if (input_message.data == NULL && input_message.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that digest length and mode match.
  HARDENED_TRY(check_digest_len(digest));

  switch (digest->mode) {
    case kHashModeSha3_224:
      return kmac_sha3_224(input_message.data, input_message.len, digest->data);
    case kHashModeSha3_256:
      return kmac_sha3_256(input_message.data, input_message.len, digest->data);
    case kHashModeSha3_384:
      return kmac_sha3_384(input_message.data, input_message.len, digest->data);
    case kHashModeSha3_512:
      return kmac_sha3_512(input_message.data, input_message.len, digest->data);
    case kHashModeSha256:
      // Call the HMAC block driver in SHA-256 mode.
      return hmac_sha256(input_message, digest);
    case kHashModeSha384:
      return sha384(input_message.data, input_message.len, digest->data);
    case kHashModeSha512:
      return sha512(input_message.data, input_message.len, digest->data);
    default:
      // Invalid hash mode.
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_xof_shake(crypto_const_byte_buf_t input_message,
                                   hash_digest_t *digest) {
  switch (digest->mode) {
    case kHashXofModeShake128:
      return kmac_shake_128(input_message.data, input_message.len, digest->data,
                            digest->len);
    case kHashXofModeShake256:
      return kmac_shake_256(input_message.data, input_message.len, digest->data,
                            digest->len);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_xof_cshake(
    crypto_const_byte_buf_t input_message,
    crypto_const_byte_buf_t function_name_string,
    crypto_const_byte_buf_t customization_string, hash_digest_t *digest) {
  // According to NIST SP 800-185 Section 3.2, cSHAKE call should use SHAKE, if
  // both `customization_string` and `function_name_string` are empty string
  if (customization_string.len == 0 && function_name_string.len == 0) {
    switch (digest->mode) {
      case kHashXofModeCshake128:
        return kmac_shake_128(input_message.data, input_message.len,
                              digest->data, digest->len);
      case kHashXofModeCshake256:
        return kmac_shake_256(input_message.data, input_message.len,
                              digest->data, digest->len);
      default:
        return OTCRYPTO_BAD_ARGS;
    }
  }

  switch (digest->mode) {
    case kHashXofModeCshake128:
      return kmac_cshake_128(
          input_message.data, input_message.len, function_name_string.data,
          function_name_string.len, customization_string.data,
          customization_string.len, digest->data, digest->len);
      break;
    case kHashXofModeCshake256:
      return kmac_cshake_256(
          input_message.data, input_message.len, function_name_string.data,
          function_name_string.len, customization_string.data,
          customization_string.len, digest->data, digest->len);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

crypto_status_t otcrypto_hash_init(hash_context_t *const ctx,
                                   hash_mode_t hash_mode) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  ctx->mode = hash_mode;
  switch (hash_mode) {
    case kHashModeSha256: {
      sha256_state_t state;
      sha256_init(&state);
      sha256_state_save(ctx, &state);
      break;
    }
    case kHashModeSha384: {
      sha384_state_t state;
      sha384_init(&state);
      sha384_state_save(ctx, &state);
      break;
    }
    case kHashModeSha512: {
      sha512_state_t state;
      sha512_init(&state);
      sha512_state_save(ctx, &state);
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hash_update(hash_context_t *const ctx,
                                     crypto_const_byte_buf_t input_message) {
  if (ctx == NULL || (input_message.data == NULL && input_message.len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }

  switch (ctx->mode) {
    case kHashModeSha256: {
      sha256_state_t state;
      sha256_state_restore(ctx, &state);
      HARDENED_TRY(
          sha256_update(&state, input_message.data, input_message.len));
      sha256_state_save(ctx, &state);
      break;
    }
    case kHashModeSha384: {
      sha384_state_t state;
      sha384_state_restore(ctx, &state);
      HARDENED_TRY(
          sha384_update(&state, input_message.data, input_message.len));
      sha384_state_save(ctx, &state);
      break;
    }
    case kHashModeSha512: {
      sha512_state_t state;
      sha512_state_restore(ctx, &state);
      HARDENED_TRY(
          sha512_update(&state, input_message.data, input_message.len));
      sha512_state_save(ctx, &state);
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hash_final(hash_context_t *const ctx,
                                    hash_digest_t *digest) {
  if (ctx == NULL || digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that digest length and mode are consistent.
  HARDENED_TRY(check_digest_len(digest));
  if (ctx->mode != digest->mode) {
    return OTCRYPTO_BAD_ARGS;
  }

  switch (ctx->mode) {
    case kHashModeSha256: {
      sha256_state_t state;
      sha256_state_restore(ctx, &state);
      HARDENED_TRY(sha256_final(&state, digest->data));
      break;
    }
    case kHashModeSha384: {
      sha384_state_t state;
      sha384_state_restore(ctx, &state);
      HARDENED_TRY(sha384_final(&state, digest->data));
      break;
    }
    case kHashModeSha512: {
      sha512_state_t state;
      sha512_state_restore(ctx, &state);
      HARDENED_TRY(sha512_final(&state, digest->data));
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}
