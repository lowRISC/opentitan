// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA384_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA384_H_

#include "stdint.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * SHA-384 message block size in bits.
   */
  kSha384MessageBlockBits = 1024,
  /**
   * SHA-384 message block size in bytes.
   */
  kSha384MessageBlockBytes = kSha384MessageBlockBits / 8,
  /**
   * SHA-384 message block size in words.
   */
  kSha384MessageBlockWords = kSha384MessageBlockBytes / sizeof(uint32_t),
  /**
   * SHA-384 state buffer size in bits (uses full 512-bit state internally).
   */
  kSha384StateBits = 512,
  /**
   * SHA-384 state buffer size in bytes.
   */
  kSha384StateBytes = kSha384StateBits / 8,
  /**
   * SHA-384 state buffer size in words.
   */
  kSha384StateWords = kSha384StateBytes / sizeof(uint32_t),
  /**
   * SHA-384 digest size in bits.
   */
  kSha384DigestBits = 384,
  /**
   * SHA-384 digest size in bytes.
   */
  kSha384DigestBytes = kSha384DigestBits / 8,
  /**
   * SHA-384 digest size in words.
   */
  kSha384DigestWords = kSha384DigestBytes / sizeof(uint32_t),
};

/**
 * A type that holds the SHA-384 message length (up to 128 bits).
 */
typedef struct sha384_message_length {
  /**
   * Lower 64 bits of the message bit-length.
   */
  uint64_t lower;
  /**
   * Upper 64 bits of the message bit-length.
   */
  uint64_t upper;
} sha384_message_length_t;

/**
 * A type that holds the context for an ongoing SHA-384 operation.
 *
 * IMPORTANT: Every member of this struct should be a word-aligned type and
 * have a size divisible by `sizeof(uint32_t)`; otherwise `sha384_state_t` will
 * not be suitable for `hardened_memcpy()`.
 */
typedef struct sha384_state {
  /**
   * Working state for a SHA-384 computation.
   */
  uint32_t H[kSha384StateWords];
  /**
   * Partial block, if any.
   */
  uint32_t partial_block[kSha384MessageBlockWords];
  /**
   * Total message length so far, in bits.
   */
  sha384_message_length_t total_len;
} sha384_state_t;

/**
 * One-shot SHA-384 hash computation.
 *
 * Returns OTCRYPTO_ASYNC_INCOMPLETE if OTBN is busy.
 *
 * @param msg Input message
 * @param msg_len Input message length in bytes
 * @param[out] digest Output buffer for digest.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha384(const uint8_t *msg, const size_t msg_len, uint32_t *digest);

/**
 * Set up a SHA-384 hash computation.
 *
 * Initializes the hash state; doesn't process anything.
 *
 * @param[out] state Hash context object to initialize.
 * @return Result of the operation (OK or error).
 */
status_t sha384_init(sha384_state_t *state);

/**
 * Process new message data for a SHA-384 hash computation.
 *
 * @param state Hash context object; updated in-place.
 * @param msg Input message.
 * @param msg_len Input message length in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha384_update(sha384_state_t *state, const uint8_t *msg,
                       const size_t msg_len);

/**
 * Finish a SHA-384 hash computation.
 *
 * @param state Hash context object.
 * @param[out] digest Output buffer for digest.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha384_final(sha384_state_t *state, uint32_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA384_H_
