// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA512_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA512_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/drivers/otbn.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
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
  /**
   * SHA-512 message block size in bits.
   */
  kSha512MessageBlockBits = 1024,
  /**
   * SHA-512 message block size in bytes.
   */
  kSha512MessageBlockBytes = kSha512MessageBlockBits / 8,
  /**
   * SHA-512 message block size in words.
   */
  kSha512MessageBlockWords = kSha512MessageBlockBytes / sizeof(uint32_t),
  /**
   * SHA-512 state buffer size in bits.
   */
  kSha512StateBits = 512,
  /**
   * SHA-512 state buffer size in bytes.
   */
  kSha512StateBytes = kSha512StateBits / 8,
  /**
   * SHA-512 state buffer size in words.
   */
  kSha512StateWords = kSha512StateBytes / sizeof(uint32_t),
  /**
   * SHA-512 digest size in bits.
   */
  kSha512DigestBits = 512,
  /**
   * SHA-512 digest size in bytes.
   */
  kSha512DigestBytes = kSha512DigestBits / 8,
  /**
   * SHA-512 digest size in words.
   */
  kSha512DigestWords = kSha512DigestBytes / sizeof(uint32_t),
};

/**
 * A type that holds the SHA-512 message length.
 *
 * The length may be up to 128 bits.
 *
 * IMPORTANT: Every member of this struct should be a word-aligned type and
 * have a size divisible by `sizeof(uint32_t)`; otherwise `sha512_state_t` will
 * not be suitable for `hardened_memcpy()`.
 */
typedef struct sha512_message_length {
  /**
   * Lower 64 bits of the message bit-length.
   */
  uint64_t lower;
  /**
   * Upper 64 bits of the message bit-length.
   */
  uint64_t upper;
} sha512_message_length_t;

/**
 * A type that holds the context for an ongoing SHA-512 operation.
 *
 * IMPORTANT: Every member of this struct should be a word-aligned type and
 * have a size divisible by `sizeof(uint32_t)`; otherwise `sha512_state_t` will
 * not be suitable for `hardened_memcpy()`.
 */
typedef struct sha512_state {
  /**
   * Working state for a SHA-512 or SHA-384 computation.
   */
  uint32_t H[kSha512StateWords];
  /**
   * Partial block, if any.
   *
   * If we get an update() with a message that isn't an even number of blocks,
   * there's no way to know if we should pad it or not until we get the next
   * update() or final(). The length of actual data in this block is always
   * (total_len % kSha512MessageBlockBytes) bytes.
   */
  uint32_t partial_block[kSha512MessageBlockWords];
  /**
   * Total message length so far, in bits.
   */
  sha512_message_length_t total_len;
} sha512_state_t;

/**
 * A type that holds the context for an ongoing SHA-384 operation.
 *
 * Since SHA-384 uses the same internal process as SHA-512, just with a
 * different initial value, the context structs are the same.
 */
typedef sha512_state_t sha384_state_t;

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
 * This interface expects the following sequence of calls:
 * - one call to sha384_init()
 * - zero or more calls to sha384_update()
 * - one call to sha384_final()
 *
 * @param[out] state Hash context object to initialize.
 * @return Result of the operation (OK or error).
 */
void sha384_init(sha384_state_t *state);

/**
 * Process new message data for a SHA-384 hash computation.
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
status_t sha384_update(sha384_state_t *state, const uint8_t *msg,
                       const size_t msg_len);

/**
 * Finish a SHA-384 hash computation.
 *
 * Incorporates the new message data into the hash context, constructs the
 * message padding and performs the final hash computation.
 *
 * The caller must ensure that at least `kSha384DigestBytes` bytes of space are
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
status_t sha384_final(sha384_state_t *state, uint32_t *digest);

/**
 * One-shot SHA-512 hash computation.
 *
 * Returns OTCRYPTO_ASYNC_INCOMPLETE if OTBN is busy.
 *
 * @param msg Input message
 * @param msg_len Input message length in bytes
 * @param[out] digest Output buffer for digest.
 * @return Result of the operation (OK or error).
 */
OT_WARN_UNUSED_RESULT
status_t sha512(const uint8_t *msg, const size_t msg_len, uint32_t *digest);

/**
 * Set up a SHA-512 hash computation.
 *
 * Initializes the hash state; doesn't process anything.
 *
 * This interface expects the following sequence of calls:
 * - one call to sha512_init()
 * - zero or more calls to sha512_update()
 * - one call to sha512_final()
 *
 * @param[out] state Hash context object to initialize.
 * @return Result of the operation (OK or error).
 */
void sha512_init(sha512_state_t *state);

/**
 * Process new message data for a SHA-512 hash computation.
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
status_t sha512_update(sha512_state_t *state, const uint8_t *msg,
                       const size_t msg_len);

/**
 * Finish a SHA-512 hash computation.
 *
 * Incorporates the new message data into the hash context, constructs the
 * message padding and performs the final hash computation.
 *
 * The caller must ensure that at least `kSha512DigestBytes` bytes of space are
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
status_t sha512_final(sha512_state_t *state, uint32_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_SHA2_SHA512_H_
