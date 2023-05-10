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
 * Return the digest size (in bytes) for given hashing mode.
 *
 * @param hash_mode Hashing mode (e.g. kHashModeSha256).
 * @param digest_len Result digest size in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
static status_t get_digest_size(hash_mode_t hash_mode, size_t *digest_len) {
  if (digest_len == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Below `digest_len` is in bytes, therefore magic values are obtained
  // after division by 8.
  switch (hash_mode) {
    case kHashModeSha3_224:
      *digest_len = 224 / 8;
      break;
    case kHashModeSha256:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_256:
      *digest_len = 256 / 8;
      break;
    case kHashModeSha384:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_384:
      *digest_len = 384 / 8;
      break;
    case kHashModeSha512:
      OT_FALLTHROUGH_INTENDED;
    case kHashModeSha3_512:
      *digest_len = 512 / 8;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  return OTCRYPTO_OK;
}

/**
 * Compute SHA256 using the HMAC hardware block.
 *
 * @param message Message to hash.
 * @param[out] digest Output digest.
 */
OT_WARN_UNUSED_RESULT
static status_t hmac_sha256(crypto_const_uint8_buf_t message,
                            crypto_uint8_buf_t *digest) {
  HARDENED_CHECK_EQ(digest->len, kHmacDigestNumBytes);

  // Initialize the hardware.
  hmac_sha256_init();

  // Pass the message and check the length.
  hmac_update(message.data, message.len);

  // Retrieve the digest and copy it to the destination buffer.
  hmac_digest_t hmac_digest;
  hmac_final(&hmac_digest);
  memcpy(digest->data, hmac_digest.digest, kHmacDigestNumBytes);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_hash(crypto_const_uint8_buf_t input_message,
                              hash_mode_t hash_mode,
                              crypto_uint8_buf_t *digest) {
  if (input_message.data == NULL && input_message.len != 0) {
    return kCryptoStatusBadArgs;
  }

  if (digest == NULL || digest->data == NULL) {
    return kCryptoStatusBadArgs;
  }

  // Check `digest->len` is consistent with `hash_mode`
  size_t expected_digest_len;
  OTCRYPTO_TRY_INTERPRET(get_digest_size(hash_mode, &expected_digest_len));
  if (expected_digest_len != digest->len) {
    return kCryptoStatusBadArgs;
  }

  switch (hash_mode) {
    case kHashModeSha3_224:
      OTCRYPTO_TRY_INTERPRET(kmac_sha3_224(input_message, digest));
      break;
    case kHashModeSha3_256:
      OTCRYPTO_TRY_INTERPRET(kmac_sha3_256(input_message, digest));
      break;
    case kHashModeSha3_384:
      OTCRYPTO_TRY_INTERPRET(kmac_sha3_384(input_message, digest));
      break;
    case kHashModeSha3_512:
      OTCRYPTO_TRY_INTERPRET(kmac_sha3_512(input_message, digest));
      break;
    case kHashModeSha256:
      // Call the HMAC block driver in SHA-256 mode.
      OTCRYPTO_TRY_INTERPRET(hmac_sha256(input_message, digest));
      break;
    case kHashModeSha384:
      OTCRYPTO_TRY_INTERPRET(
          sha384(input_message.data, input_message.len, digest->data));
      break;
    case kHashModeSha512:
      OTCRYPTO_TRY_INTERPRET(
          sha512(input_message.data, input_message.len, digest->data));
      break;
    default:
      // Unrecognized hash mode.
      return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}

crypto_status_t otcrypto_xof(crypto_const_uint8_buf_t input_message,
                             xof_mode_t xof_mode,
                             crypto_const_uint8_buf_t function_name_string,
                             crypto_const_uint8_buf_t customization_string,
                             size_t required_output_len,
                             crypto_uint8_buf_t *digest) {
  // TODO: (#16410) Add error checks
  if (required_output_len != digest->len) {
    return kCryptoStatusBadArgs;
  }

  // According to NIST SP 800-185 Section 3.2, cSHAKE call should use SHAKE, if
  // both `customization_string` and `function_name_string` are empty string
  if (customization_string.len == 0 && function_name_string.len == 0) {
    if (xof_mode == kXofModeSha3Cshake128) {
      xof_mode = kXofModeSha3Shake128;
    } else if (xof_mode == kXofModeSha3Cshake256) {
      xof_mode = kXofModeSha3Shake256;
    }
  }

  switch (xof_mode) {
    case kXofModeSha3Shake128:
      OTCRYPTO_TRY_INTERPRET(kmac_shake_128(input_message, digest));
      break;
    case kXofModeSha3Shake256:
      OTCRYPTO_TRY_INTERPRET(kmac_shake_256(input_message, digest));
      break;
    case kXofModeSha3Cshake128:
      OTCRYPTO_TRY_INTERPRET(kmac_cshake_128(
          input_message, function_name_string, customization_string, digest));
      break;
    case kXofModeSha3Cshake256:
      OTCRYPTO_TRY_INTERPRET(kmac_cshake_256(
          input_message, function_name_string, customization_string, digest));
      break;
    default:
      return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}

crypto_status_t otcrypto_hash_init(hash_context_t *const ctx,
                                   hash_mode_t hash_mode) {
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
      return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}

crypto_status_t otcrypto_hash_update(hash_context_t *const ctx,
                                     crypto_const_uint8_buf_t input_message) {
  if (input_message.data == NULL && input_message.len != 0) {
    return kCryptoStatusBadArgs;
  }

  switch (ctx->mode) {
    case kHashModeSha256: {
      sha256_state_t state;
      sha256_state_restore(ctx, &state);
      OTCRYPTO_TRY_INTERPRET(
          sha256_update(&state, input_message.data, input_message.len));
      sha256_state_save(ctx, &state);
      break;
    }
    case kHashModeSha384: {
      sha384_state_t state;
      sha384_state_restore(ctx, &state);
      OTCRYPTO_TRY_INTERPRET(
          sha384_update(&state, input_message.data, input_message.len));
      sha384_state_save(ctx, &state);
      break;
    }
    case kHashModeSha512: {
      sha512_state_t state;
      sha512_state_restore(ctx, &state);
      OTCRYPTO_TRY_INTERPRET(
          sha512_update(&state, input_message.data, input_message.len));
      sha512_state_save(ctx, &state);
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}

crypto_status_t otcrypto_hash_final(hash_context_t *const ctx,
                                    crypto_uint8_buf_t *digest) {
  if (digest == NULL || digest->data == NULL) {
    return kCryptoStatusBadArgs;
  }

  // Check `digest->len` is consistent with `ctx->mode`
  size_t expected_digest_len;
  OTCRYPTO_TRY_INTERPRET(get_digest_size(ctx->mode, &expected_digest_len));
  if (expected_digest_len != digest->len) {
    return kCryptoStatusBadArgs;
  }

  switch (ctx->mode) {
    case kHashModeSha256: {
      sha256_state_t state;
      sha256_state_restore(ctx, &state);
      OTCRYPTO_TRY_INTERPRET(sha256_final(&state, digest->data));
      break;
    }
    case kHashModeSha384: {
      sha384_state_t state;
      sha384_state_restore(ctx, &state);
      OTCRYPTO_TRY_INTERPRET(sha384_final(&state, digest->data));
      break;
    }
    case kHashModeSha512: {
      sha512_state_t state;
      sha512_state_restore(ctx, &state);
      OTCRYPTO_TRY_INTERPRET(sha512_final(&state, digest->data));
      break;
    }
    default:
      // Unrecognized or unsupported hash mode.
      return kCryptoStatusBadArgs;
  }

  return kCryptoStatusOK;
}
