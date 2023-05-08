// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA256_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA256_H_

#include "stdint.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * SHA-256 message block size in bits.
   */
  kSha256MessageBlockBits = 512,
  /**
   * SHA-256 message block size in bytes.
   */
  kSha256MessageBlockBytes = kSha256MessageBlockBits / 8,
  /**
   * SHA-256 message block size in words.
   */
  kSha256MessageBlockWords = kSha256MessageBlockBytes / sizeof(uint32_t),
  /**
   * SHA-256 state buffer size in bits.
   */
  kSha256StateBits = 256,
  /**
   * SHA-256 state buffer size in bytes.
   */
  kSha256StateBytes = kSha256StateBits / 8,
  /**
   * SHA-256 state buffer size in words.
   */
  kSha256StateWords = kSha256StateBytes / sizeof(uint32_t),
  /**
   * SHA-256 digest size in bits.
   */
  kSha256DigestBits = 256,
  /**
   * SHA-256 digest size in bytes.
   */
  kSha256DigestBytes = kSha256DigestBits / 8,
  /**
   * SHA-256 digest size in words.
   */
  kSha256DigestWords = kSha256DigestBytes / sizeof(uint32_t),
};

/**
 * A type that holds the context for an ongoing SHA-256 operation.
 *
 * IMPORTANT: Every member of this struct should be a word-aligned type and
 * have a size divisible by `sizeof(uint32_t)`; otherwise `sha256_state_t` will
 * not be suitable for `hardened_memcpy()`.
 */
typedef struct sha256_state {
  /**
   * Working state for a SHA-256 or SHA-384 computation.
   */
  uint32_t H[kSha256StateWords];
  /**
   * Partial block, if any.
   *
   * If we get an update() with a message that isn't an even number of blocks,
   * there's no way to know if we should pad it or not until we get the next
   * update() or final(). The length of actual data in this block is always
   * (total_len % kSha256MessageBlockBytes) bytes.
   */
  uint32_t partial_block[kSha256MessageBlockWords];
  /**
   * Total message length so far, in bits.
   */
  uint64_t total_len;
} sha256_state_t;

/**
 * One-shot SHA-256 hash computation.
 *
 * Returns OTCRYPTO_ASYNC_INCOMPLETE if OTBN is busy.
 *
 * @param msg Input message
 * @param msg_len Input message length in bytes
 * @param[out] digest Output buffer for digest.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha256(const uint8_t *msg, const size_t msg_len, uint8_t *digest);

/**
 * Set up a SHA-256 hash computation.
 *
 * Initializes the hash state; doesn't process anything.
 *
 * This interface expects the following sequence of calls:
 * - one call to sha256_init()
 * - zero or more calls to sha256_update()
 * - one call to sha256_final()
 *
 * @param[out] state Hash context object to initialize.
 * @return Result of the operation (OK or error).
 */
void sha256_init(sha256_state_t *state);

/**
 * Process new message data for a SHA-256 hash computation.
 *
 * Incorporates the new message data into the hash context.
 *
 * Returns OTCRYPTO_ASYNC_INCOMPLETE if OTBN is busy.
 *
 * @param state Hash context object; updated in-place.
 * @param msg Input message.
 * @param msg_len Input message length in bytes.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha256_update(sha256_state_t *state, const uint8_t *msg,
                       const size_t msg_len);

/**
 * Finish a SHA-256 hash computation.
 *
 * Incorporates the new message data into the hash context, constructs the
 * message padding and performs the final hash computation.
 *
 * The caller must ensure that at least `kSha256DigestBytes` bytes of space are
 * available at the location pointed to by `digest`.
 *
 * Returns OTCRYPTO_ASYNC_INCOMPLETE if OTBN is busy.
 *
 * @param state Hash context object.
 * @param msg Input message
 * @param msg_len Input message length in bytes
 * @param[out] digest Output buffer for digest.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha256_final(sha256_state_t *state, uint8_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA256_H_
