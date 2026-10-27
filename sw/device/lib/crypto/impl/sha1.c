// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/sha1.h"

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/impl/cmvp.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('s', 'h', '1')

/**
 * Plain software implementation of SHA-1 (FIPS 180-4) and HMAC-SHA-1
 * (RFC 2104 / FIPS 198-1).
 *
 * Note: This implementation runs in plain software on Ibex without hardware
 * acceleration and is NOT hardened against fault injection (FI) or
 * side-channel analysis (SCA).
 */

enum {
  /**
   * SHA-1 message block size in bits.
   */
  kSha1BlockBits = 512,
  /**
   * SHA-1 message block size in bytes.
   */
  kSha1BlockBytes = kSha1BlockBits / 8,
  /**
   * SHA-1 message block size in 32-bit words.
   */
  kSha1BlockWords = kSha1BlockBytes / sizeof(uint32_t),
  /**
   * SHA-1 digest size in bytes.
   */
  kSha1DigestBytes = 20,
  /**
   * SHA-1 digest size in 32-bit words.
   */
  kSha1DigestWords = kSha1DigestBytes / sizeof(uint32_t),
  /**
   * Maximum message byte length for SHA-1: 2^64 - 1 bits = 2^61 - 1 bytes.
   * The upper 32 bits of the byte count must not exceed 0x1fffffff.
   */
  kSha1MaxMessageBytesHi = 0x1fffffffu,
};

/**
 * Internal SHA-1 streaming state.
 *
 * Uses only 32-bit fields so size and alignment are identical across 32-bit
 * device and 64-bit host builds.
 */
typedef struct sha1_state {
  /**
   * Working state H[0..4].
   */
  uint32_t h[kSha1DigestWords];
  /**
   * Buffered partial message block (up to 64 bytes).
   */
  uint32_t partial_block[kSha1BlockWords];
  /**
   * Low 32 bits of total processed message length in bytes.
   */
  uint32_t total_len_lo;
  /**
   * High 32 bits of total processed message length in bytes.
   */
  uint32_t total_len_hi;
  /**
   * Hardened boolean indicating whether this context is initialized.
   */
  uint32_t initialized;
} sha1_state_t;

OT_ASSERT_MEMBER_OFFSET(sha1_state_t, h, 0);
OT_ASSERT_MEMBER_OFFSET(sha1_state_t, partial_block, 20);
OT_ASSERT_MEMBER_OFFSET(sha1_state_t, total_len_lo, 84);
OT_ASSERT_MEMBER_OFFSET(sha1_state_t, total_len_hi, 88);
OT_ASSERT_MEMBER_OFFSET(sha1_state_t, initialized, 92);
OT_ASSERT_SIZE(sha1_state_t, 96);

static_assert(sizeof(otcrypto_sha1_context_t) == sizeof(sha1_state_t),
              "otcrypto_sha1_context_t size must match sha1_state_t");
static_assert(alignof(otcrypto_sha1_context_t) == alignof(sha1_state_t),
              "otcrypto_sha1_context_t alignment must match sha1_state_t");

/**
 * Internal HMAC-SHA-1 streaming state.
 */
typedef struct hmac_sha1_state {
  /**
   * Inner SHA-1 streaming state.
   */
  sha1_state_t inner;
  /**
   * Outer padded key block (K_0 ^ opad), stored as 16 32-bit words (64 bytes).
   */
  uint32_t opad[kSha1BlockWords];
} hmac_sha1_state_t;

OT_ASSERT_MEMBER_OFFSET(hmac_sha1_state_t, inner, 0);
OT_ASSERT_MEMBER_OFFSET(hmac_sha1_state_t, opad, 96);
OT_ASSERT_SIZE(hmac_sha1_state_t, 160);

static_assert(sizeof(otcrypto_hmac_sha1_context_t) == sizeof(hmac_sha1_state_t),
              "otcrypto_hmac_sha1_context_t size must match hmac_sha1_state_t");
static_assert(
    alignof(otcrypto_hmac_sha1_context_t) == alignof(hmac_sha1_state_t),
    "otcrypto_hmac_sha1_context_t alignment must match hmac_sha1_state_t");

/**
 * Read a 32-bit big-endian word from a byte buffer.
 */
static inline uint32_t read_be32(const uint8_t in[4]) {
  return ((uint32_t)in[0] << 24) | ((uint32_t)in[1] << 16) |
         ((uint32_t)in[2] << 8) | (uint32_t)in[3];
}

/**
 * Write a 32-bit word in big-endian order to a byte buffer.
 */
static inline void write_be32(uint32_t val, uint8_t out[4]) {
  out[0] = (uint8_t)(val >> 24);
  out[1] = (uint8_t)(val >> 16);
  out[2] = (uint8_t)(val >> 8);
  out[3] = (uint8_t)val;
}

/**
 * 32-bit left rotation.
 */
static inline uint32_t rotl32(uint32_t x, uint32_t n) {
  return (x << n) | (x >> (32u - n));
}

/**
 * Process a single 64-byte (512-bit) SHA-1 message block.
 *
 * @param state Current 5-word SHA-1 working state (updated in place).
 * @param block Pointer to a 64-byte message block.
 */
static void sha1_process_block(uint32_t state[kSha1DigestWords],
                               const uint8_t block[kSha1BlockBytes]) {
  uint32_t w[16];
  for (size_t i = 0; i < 16; ++i) {
    w[i] = read_be32(&block[i * 4]);
  }

  uint32_t a = state[0];
  uint32_t b = state[1];
  uint32_t c = state[2];
  uint32_t d = state[3];
  uint32_t e = state[4];

  for (size_t t = 0; t < 80; ++t) {
    uint32_t wt;
    if (t < 16) {
      wt = w[t];
    } else {
      wt = rotl32(w[(t - 3) & 0x0f] ^ w[(t - 8) & 0x0f] ^ w[(t - 14) & 0x0f] ^
                      w[t & 0x0f],
                  1);
      w[t & 0x0f] = wt;
    }

    uint32_t f;
    uint32_t k;
    if (t < 20) {
      f = (b & c) | ((~b) & d);
      k = 0x5a827999u;
    } else if (t < 40) {
      f = b ^ c ^ d;
      k = 0x6ed9eba1u;
    } else if (t < 60) {
      f = (b & c) | (b & d) | (c & d);
      k = 0x8f1bbcdcu;
    } else {
      f = b ^ c ^ d;
      k = 0xca62c1d6u;
    }

    uint32_t temp = rotl32(a, 5) + f + e + k + wt;
    e = d;
    d = c;
    c = rotl32(b, 30);
    b = a;
    a = temp;
  }

  state[0] += a;
  state[1] += b;
  state[2] += c;
  state[3] += d;
  state[4] += e;
}

/**
 * Initialize an internal SHA-1 state struct.
 */
static void sha1_state_init(sha1_state_t *state) {
  memset(state, 0, sizeof(sha1_state_t));
  state->h[0] = 0x67452301u;
  state->h[1] = 0xefcdab89u;
  state->h[2] = 0x98badcfeu;
  state->h[3] = 0x10325476u;
  state->h[4] = 0xc3d2e1f0u;
  state->initialized = kHardenedBoolTrue;
}

/**
 * Update an internal SHA-1 state with message bytes.
 */
static status_t sha1_state_update(sha1_state_t *state, const uint8_t *data,
                                  size_t len) {
  if (launder32(state->initialized) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(state->initialized, kHardenedBoolTrue);

  if (len == 0) {
    return OTCRYPTO_OK;
  }

  // Current buffered byte count in partial_block.
  size_t buffered = state->total_len_lo & (kSha1BlockBytes - 1);

  // Update 64-bit byte counter and check for 2^64 - 1 bit overflow.
  uint32_t new_lo = state->total_len_lo + (uint32_t)len;
  uint32_t carry = (new_lo < state->total_len_lo) ? 1u : 0u;
  uint32_t new_hi = state->total_len_hi + carry;
  if (new_hi > kSha1MaxMessageBytesHi) {
    return OTCRYPTO_BAD_ARGS;
  }
  state->total_len_lo = new_lo;
  state->total_len_hi = new_hi;

  uint8_t *partial_bytes = (uint8_t *)state->partial_block;

  // If we have buffered bytes and enough new input to complete a block,
  // process that block first.
  if (buffered > 0) {
    size_t space = kSha1BlockBytes - buffered;
    if (len < space) {
      memcpy(&partial_bytes[buffered], data, len);
      return OTCRYPTO_OK;
    }
    memcpy(&partial_bytes[buffered], data, space);
    sha1_process_block(state->h, partial_bytes);
    data += space;
    len -= space;
  }

  // Process full 64-byte blocks directly from the input buffer.
  while (len >= kSha1BlockBytes) {
    sha1_process_block(state->h, data);
    data += kSha1BlockBytes;
    len -= kSha1BlockBytes;
  }

  // Buffer any remaining trailing bytes.
  if (len > 0) {
    memcpy(partial_bytes, data, len);
  }

  return OTCRYPTO_OK;
}

/**
 * Finalize an internal SHA-1 state and write the 20-byte digest to `out_words`.
 */
static status_t sha1_state_final(sha1_state_t *state,
                                 uint32_t out_words[kSha1DigestWords]) {
  if (launder32(state->initialized) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(state->initialized, kHardenedBoolTrue);

  size_t buffered = state->total_len_lo & (kSha1BlockBytes - 1);
  uint8_t *partial_bytes = (uint8_t *)state->partial_block;

  // Append the '1' bit (0x80 byte).
  partial_bytes[buffered++] = 0x80u;

  // If there is not enough room for the 64-bit bit-length (8 bytes), pad the
  // current block with zeros, process it, and start a new zero block.
  if (buffered > kSha1BlockBytes - 8) {
    memset(&partial_bytes[buffered], 0, kSha1BlockBytes - buffered);
    sha1_process_block(state->h, partial_bytes);
    buffered = 0;
  }

  // Zero-pad up to the final 8 bytes of the block.
  memset(&partial_bytes[buffered], 0, (kSha1BlockBytes - 8) - buffered);

  // Append the 64-bit message length in bits in big-endian byte order.
  uint32_t bit_len_hi =
      (state->total_len_hi << 3) | (state->total_len_lo >> 29);
  uint32_t bit_len_lo = state->total_len_lo << 3;
  write_be32(bit_len_hi, &partial_bytes[kSha1BlockBytes - 8]);
  write_be32(bit_len_lo, &partial_bytes[kSha1BlockBytes - 4]);

  sha1_process_block(state->h, partial_bytes);

  // Serialize the 5 digest words in big-endian byte order into `out_words`,
  // matching the byte layout produced by the OpenTitan SHA-2/SHA-3 drivers.
  uint8_t *digest_bytes = (uint8_t *)out_words;
  for (size_t i = 0; i < kSha1DigestWords; ++i) {
    write_be32(state->h[i], &digest_bytes[i * sizeof(uint32_t)]);
  }

  // Clear state so a finalized context cannot be reused without re-init.
  memset(state, 0, sizeof(sha1_state_t));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_sha1(const otcrypto_const_byte_buf_t *message,
                                otcrypto_hash_digest_t *digest) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA1);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (message == NULL || (message->data == NULL && message->len != 0)) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(digest->len) != kSha1DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kSha1DigestWords);
  digest->mode = kOtcryptoHashModeSha1;

  sha1_state_t state;
  sha1_state_init(&state);
  HARDENED_TRY(sha1_state_update(&state, message->data, message->len));
  return otcrypto_eval_exit(sha1_state_final(&state, digest->data));
}

otcrypto_status_t otcrypto_sha1_init(otcrypto_sha1_context_t *ctx) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA1_INIT);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  sha1_state_t *state = (sha1_state_t *)ctx->data;
  sha1_state_init(state);
  return otcrypto_eval_exit(OTCRYPTO_OK);
}

otcrypto_status_t otcrypto_sha1_update(
    otcrypto_sha1_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA1_UPDATE);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || input_message == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (input_message->data == NULL && input_message->len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  sha1_state_t *state = (sha1_state_t *)ctx->data;
  return otcrypto_eval_exit(
      sha1_state_update(state, input_message->data, input_message->len));
}

otcrypto_status_t otcrypto_sha1_final(otcrypto_sha1_context_t *ctx,
                                      otcrypto_hash_digest_t *digest) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_SHA1_FINAL);
  OTCRYPTO_LOCKED_STATE_CHECK();
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || digest == NULL || digest->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(digest->len) != kSha1DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest->len, kSha1DigestWords);

  digest->mode = kOtcryptoHashModeSha1;
  sha1_state_t *state = (sha1_state_t *)ctx->data;
  return otcrypto_eval_exit(sha1_state_final(state, digest->data));
}

/**
 * Internal helper for HMAC-SHA-1 initialization (without setting CMVP
 * indicator so one-shot `otcrypto_hmac_sha1` can set its own indicator).
 */
static status_t hmac_sha1_init_internal(otcrypto_hmac_sha1_context_t *ctx,
                                        const otcrypto_blinded_key_t *key) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || key == NULL || key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  // Key must be configured for HMAC-SHA-1, reside in software (not sideloaded),
  // and have a non-zero key length.
  if (key->config.key_mode != kOtcryptoKeyModeHmacSha1 ||
      key->config.hw_backed != kHardenedBoolFalse ||
      key->config.key_length == 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Note: Any valid security_level is accepted for API compatibility, even
  // though this plain software implementation provides no SCA/FI protection.
  if (key->config.security_level != kOtcryptoKeySecurityLevelLow &&
      key->config.security_level != kOtcryptoKeySecurityLevelMedium &&
      key->config.security_level != kOtcryptoKeySecurityLevelHigh) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the blinded key.
  if (launder32(otcrypto_integrity_blinded_key_check(key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(otcrypto_integrity_blinded_key_check(key),
                    kHardenedBoolTrue);

  // Verify keyblob length matches the key configuration.
  uint32_t key_words = ceil_div(key->config.key_length, sizeof(uint32_t));
  if (key->keyblob_length !=
      keyblob_num_words(key->config) * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Prepare the 64-byte key block K_0.
  uint32_t k0_words[kSha1BlockWords];
  memset(k0_words, 0, sizeof(k0_words));
  uint8_t *k0_bytes = (uint8_t *)k0_words;

  if (key->config.key_length > kSha1BlockBytes) {
    // Keys longer than the SHA-1 block size (64 bytes) are hashed with SHA-1
    // to a 20-byte key first, then zero-padded to 64 bytes (RFC 2104).
    uint32_t unmasked_key[key_words];
    HARDENED_TRY(keyblob_key_unmask(key, key_words, unmasked_key));

    sha1_state_t key_hash_state;
    sha1_state_init(&key_hash_state);
    HARDENED_TRY(sha1_state_update(&key_hash_state,
                                   (const uint8_t *)unmasked_key,
                                   key->config.key_length));
    HARDENED_TRY(sha1_state_final(&key_hash_state, k0_words));
    memset(unmasked_key, 0, sizeof(unmasked_key));
  } else {
    uint32_t unmasked_key[key_words];
    HARDENED_TRY(keyblob_key_unmask(key, key_words, unmasked_key));
    memcpy(k0_bytes, unmasked_key, key->config.key_length);
    memset(unmasked_key, 0, sizeof(unmasked_key));
  }

  hmac_sha1_state_t *hmac_state = (hmac_sha1_state_t *)ctx->data;
  uint8_t ipad[kSha1BlockBytes];
  uint8_t *opad_bytes = (uint8_t *)hmac_state->opad;
  for (size_t i = 0; i < kSha1BlockBytes; ++i) {
    ipad[i] = k0_bytes[i] ^ 0x36u;
    opad_bytes[i] = k0_bytes[i] ^ 0x5cu;
  }
  memset(k0_words, 0, sizeof(k0_words));

  sha1_state_init(&hmac_state->inner);
  status_t status = sha1_state_update(&hmac_state->inner, ipad, sizeof(ipad));
  memset(ipad, 0, sizeof(ipad));
  return status;
}

static status_t hmac_sha1_update_internal(
    otcrypto_hmac_sha1_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || input_message == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (input_message->data == NULL && input_message->len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif

  hmac_sha1_state_t *hmac_state = (hmac_sha1_state_t *)ctx->data;
  return sha1_state_update(&hmac_state->inner, input_message->data,
                           input_message->len);
}

static status_t hmac_sha1_final_internal(otcrypto_hmac_sha1_context_t *ctx,
                                         otcrypto_word32_buf_t *tag) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (ctx == NULL || tag == NULL || tag->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(tag->len) != kSha1DigestWords) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(tag->len, kSha1DigestWords);

  hmac_sha1_state_t *hmac_state = (hmac_sha1_state_t *)ctx->data;

  // Finalize the inner hash: H((K_0 ^ ipad) || message).
  uint32_t inner_digest[kSha1DigestWords];
  HARDENED_TRY(sha1_state_final(&hmac_state->inner, inner_digest));

  // Compute the outer hash: H((K_0 ^ opad) || inner_digest).
  sha1_state_t outer;
  sha1_state_init(&outer);
  HARDENED_TRY(sha1_state_update(&outer, (const uint8_t *)hmac_state->opad,
                                 kSha1BlockBytes));
  HARDENED_TRY(sha1_state_update(&outer, (const uint8_t *)inner_digest,
                                 kSha1DigestBytes));
  status_t status = sha1_state_final(&outer, tag->data);

  memset(inner_digest, 0, sizeof(inner_digest));
  memset(hmac_state, 0, sizeof(hmac_sha1_state_t));
  return status;
}

otcrypto_status_t otcrypto_hmac_sha1_init(otcrypto_hmac_sha1_context_t *ctx,
                                          const otcrypto_blinded_key_t *key) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_SHA1_INIT);
  OTCRYPTO_LOCKED_STATE_CHECK();
  return otcrypto_eval_exit(hmac_sha1_init_internal(ctx, key));
}

otcrypto_status_t otcrypto_hmac_sha1_update(
    otcrypto_hmac_sha1_context_t *ctx,
    const otcrypto_const_byte_buf_t *input_message) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_SHA1_UPDATE);
  OTCRYPTO_LOCKED_STATE_CHECK();
  return otcrypto_eval_exit(hmac_sha1_update_internal(ctx, input_message));
}

otcrypto_status_t otcrypto_hmac_sha1_final(otcrypto_hmac_sha1_context_t *ctx,
                                           otcrypto_word32_buf_t *tag) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_SHA1_FINAL);
  OTCRYPTO_LOCKED_STATE_CHECK();
  return otcrypto_eval_exit(hmac_sha1_final_internal(ctx, tag));
}

otcrypto_status_t otcrypto_hmac_sha1(
    const otcrypto_blinded_key_t *key,
    const otcrypto_const_byte_buf_t *input_message,
    otcrypto_word32_buf_t *tag) {
  OTCRYPTO_SET_CMVP_INDICATOR(OTCRYPTO_FUNCTION_HMAC_SHA1);
  OTCRYPTO_LOCKED_STATE_CHECK();
  otcrypto_hmac_sha1_context_t ctx;
  HARDENED_TRY(hmac_sha1_init_internal(&ctx, key));
  HARDENED_TRY(hmac_sha1_update_internal(&ctx, input_message));
  return otcrypto_eval_exit(hmac_sha1_final_internal(&ctx, tag));
}
