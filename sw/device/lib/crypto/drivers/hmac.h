// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#include "hmac_regs.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /* Size of a SHA256 or HMAC-SHA256 digest in bytes. */
  kHmacSha256DigestBytes = 256 / 8,
  /* Size of a SHA256 or HMAC-SHA256 digest in 32-bit words. */
  kHmacSha256DigestWords = kHmacSha256DigestBytes / sizeof(uint32_t),
  /* Size of a SHA384 or HMAC-SHA384 digest in bytes. */
  kHmacSha384DigestBytes = 384 / 8,
  /* Size of a SHA384 or HMAC-SHA384 digest in 32-bit words. */
  kHmacSha384DigestWords = kHmacSha384DigestBytes / sizeof(uint32_t),
  /* Size of a SHA512 or HMAC-SHA512 digest in bytes. */
  kHmacSha512DigestBytes = 512 / 8,
  /* Size of a SHA512 or HMAC-SHA512 digest in 32-bit words. */
  kHmacSha512DigestWords = kHmacSha512DigestBytes / sizeof(uint32_t),
  /* Size of the underlying message block for SHA256 in bytes. */
  kHmacSha256BlockBytes = 512 / 8,
  /* Size of the underlying message block for SHA256 in 32-bit words. */
  kHmacSha256BlockWords = kHmacSha256BlockBytes / sizeof(uint32_t),
  /* Size of the underlying message block for SHA384 in bytes. */
  kHmacSha384BlockBytes = 1024 / 8,
  /* Size of the underlying message block for SHA384 in 32-bit words. */
  kHmacSha384BlockWords = kHmacSha384BlockBytes / sizeof(uint32_t),
  /* Size of the underlying message block for SHA512 in bytes. */
  kHmacSha512BlockBytes = 1024 / 8,
  /* Size of the underlying message block for SHA512 in 32-bit words. */
  kHmacSha512BlockWords = kHmacSha512BlockBytes / sizeof(uint32_t),
  /* Maximum digest size supported by the hardware, in bytes. */
  kHmacMaxDigestBytes = kHmacSha512DigestBytes,
  /* Maximum digest size supported by the hardware, in 32-bit words. */
  kHmacMaxDigestWords = kHmacMaxDigestBytes / sizeof(uint32_t),
  /* Maximum block size supported by the hardware, in bytes. */
  kHmacMaxBlockBytes = kHmacSha512BlockBytes,
  /* Maximum block size supported by the hardware, in 32-bit words. */
  kHmacMaxBlockWords = kHmacMaxBlockBytes / sizeof(uint32_t),
};

/**
 * A context struct maintained for streaming operations.
 */
typedef struct hmac_ctx {
  // A copy of `CFG` register used during resumption.
  uint32_t cfg_reg;
  // A copy of `KEY` to be used during start or resumption.
  uint32_t key[kHmacMaxBlockWords];
  size_t key_wordlen;
  // The internal (message) block size of SHA-2 for this operation.
  size_t msg_block_wordlen;
  size_t digest_wordlen;
  // The following fields are saved and restored during streaming.
  uint32_t H[kHmacMaxDigestWords];
  uint32_t lower;
  uint32_t upper;
  uint32_t partial_block[kHmacMaxBlockWords];
  // The number of valid bytes in `partial_block`.
  size_t partial_block_bytelen;
} hmac_ctx_t;

/**
 * One-shot SHA256 hash computation.
 *
 * @param msg Input message.
 * @param msg_len Message length in bytes.
 * @param[out] digest Resulting digest (`kHmacSha256DigestWords` words).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hash_sha256(const uint8_t *msg, size_t msg_len, uint32_t *digest);

/**
 * One-shot SHA384 hash computation.
 *
 * @param msg Input message.
 * @param msg_len Message length in bytes.
 * @param[out] digest Resulting digest (`kHmacSha384DigestWords` words).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hash_sha384(const uint8_t *msg, size_t msg_len, uint32_t *digest);

/**
 * One-shot SHA512 hash computation.
 *
 * @param msg Input message.
 * @param msg_len Message length in bytes.
 * @param[out] digest Resulting digest (`kHmacSha512DigestWords` words).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hash_sha512(const uint8_t *msg, size_t msg_len, uint32_t *digest);

/**
 * One-shot HMAC-SHA256 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha256BlockWords` words).
 * @param msg Input message.
 * @param msg_len Message length in bytes.
 * @param[out] tag Authentication tag (`kHmacSha256DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha256(const uint32_t *key_block, const uint8_t *msg,
                          size_t msg_len, uint32_t *tag);

/**
 * One-shot HMAC-SHA384 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha384BlockWords` words).
 * @param msg Input message.
 * @param msg_len Message length in bytes.
 * @param[out] tag Authentication tag (`kHmacSha384DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha384(const uint32_t *key_block, const uint8_t *msg,
                          size_t msg_len, uint32_t *tag);

/**
 * One-shot HMAC-SHA512 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha512BlockWords` words).
 * @param msg Input message.
 * @param msg_len Message length in bytes.
 * @param[out] tag Authentication tag (`kHmacSha512DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha512(const uint32_t *key_block, const uint8_t *msg,
                          size_t msg_len, uint32_t *tag);

/**
 * Initializes the context for a streaming SHA256 hash computation.
 *
 * @param[out] ctx Initialized context object.
 */
void hmac_hash_sha256_init(hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming SHA384 hash computation.
 *
 * @param[out] ctx Initialized context object.
 */
void hmac_hash_sha384_init(hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming SHA512 hash computation.
 *
 * @param[out] ctx Initialized context object.
 */
void hmac_hash_sha512_init(hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming HMAC-SHA256 computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha256BlockWords` words).
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha256_init(const uint32_t *key_block, hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming HMAC-SHA256 computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha256BlockWords` words).
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha256_init(const uint32_t *key_block, hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming HMAC-SHA384 computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha384BlockWords` words).
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha384_init(const uint32_t *key_block, hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming HMAC-SHA512 computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key_block Input key block (`kHmacSha512BlockWords` words).
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha512_init(const uint32_t *key_block, hmac_ctx_t *ctx);

/**
 * Update the context with additional messsage data.
 *
 * This function can be used with all SHA2 and HMAC operations, and may be
 * called multiple times between init() and final().
 *
 * @param ctx Context object referring to a particular SHA-2/HMAC stream.
 * @param data Incoming message bytes to be processed into the stream.
 * @param len Size of the `data` buffer in bytes.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_update(hmac_ctx_t *ctx, const uint8_t *data, size_t len);

/**
 * Finalize the SHA-2/HMAC stream and return the digest/tag.
 *
 * The caller must ensure that `ctx->digest_wordlen` words of space are
 * available at the buffer pointed to by `digest`.
 *
 * @param ctx Context object referring to a particular stream.
 * @param[out] digest Resulting digest or authentication tag.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_final(hmac_ctx_t *ctx, uint32_t *digest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_
