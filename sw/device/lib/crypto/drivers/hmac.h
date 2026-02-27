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

#include "hw/top/hmac_regs.h"

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
 * The HMAC key structure.
 */
typedef struct hmac_key {
  /**
   * The length of the key (in 32-bit words).
   */
  size_t key_len;
  /**
   * Key storage buffer.
   */
  uint32_t key_block[kHmacMaxBlockWords];
  /**
   * Checksum of this HMAC key structure.
   */
  uint32_t checksum;
} hmac_key_t;

/**
 * A context struct maintained for streaming operations.
 */
typedef struct hmac_ctx {
  // A copy of `CFG` register used during resumption.
  uint32_t cfg_reg;
  // A copy of `KEY` to be used during start or resumption.
  hmac_key_t key;
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
 * @param msg Input message buffer.
 * @param[out] digest Resulting digest (`kHmacSha256DigestWords` words).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hash_sha256(const otcrypto_const_byte_buf_t *msg,
                          uint32_t *digest);

/**
 * One-shot SHA384 hash computation.
 *
 * @param msg Input message buffer.
 * @param[out] digest Resulting digest (`kHmacSha384DigestWords` words).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hash_sha384(const otcrypto_const_byte_buf_t *msg,
                          uint32_t *digest);

/**
 * One-shot SHA512 hash computation.
 *
 * @param msg Input message buffer.
 * @param[out] digest Resulting digest (`kHmacSha512DigestWords` words).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hash_sha512(const otcrypto_const_byte_buf_t *msg,
                          uint32_t *digest);

/**
 * One-shot HMAC-SHA256 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key HMAC key.
 * @param msg Input message buffer.
 * @param[out] tag Authentication tag (`kHmacSha256DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha256(const hmac_key_t *key,
                          const otcrypto_const_byte_buf_t *msg,
                          otcrypto_word32_buf_t *tag);

/**
 * Redundant implementation for a one-shot HMAC-SHA256 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * To be used together with hmac_hmac_sha256() to mitigate FI attacks. This
 * implementation is different to hmac_hmac_sha256() as it manually assembles
 * the HMAC functionality using SHA256. By using two different HMAC
 * implementations, injecting two identical faults affect different parts during
 * the HMAC compuation, which can be detected.
 *
 * @param key HMAC key.
 * @param msg Input message buffer.
 * @param[out] tag Authentication tag (`kHmacSha256DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha256_redundant(const hmac_key_t *key,
                                    const otcrypto_const_byte_buf_t *msg,
                                    otcrypto_word32_buf_t *tag);

/**
 * One-shot HMAC-SHA384 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key HMAC key.
 * @param msg Input message buffer.
 * @param[out] tag Authentication tag (`kHmacSha384DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha384(const hmac_key_t *key,
                          const otcrypto_const_byte_buf_t *msg,
                          otcrypto_word32_buf_t *tag);

/**
 * Redundant implementation for a one-shot HMAC-SHA384 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * To be used together with hmac_hmac_sha384() to mitigate FI attacks. This
 * implementation is different to hmac_hmac_sha384() as it manually assembles
 * the HMAC functionality using SHA384. By using two different HMAC
 * implementations, injecting two identical faults affect different parts during
 * the HMAC compuation, which can be detected.
 *
 * @param key HMAC key.
 * @param msg Input message buffer.
 * @param[out] tag Authentication tag (`kHmacSha384DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha384_redundant(const hmac_key_t *key,
                                    const otcrypto_const_byte_buf_t *msg,
                                    otcrypto_word32_buf_t *tag);

/**
 * One-shot HMAC-SHA512 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key HMAC key.
 * @param msg Input message buffer.
 * @param[out] tag Authentication tag (`kHmacSha512DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha512(const hmac_key_t *key,
                          const otcrypto_const_byte_buf_t *msg,
                          otcrypto_word32_buf_t *tag);

/**
 * Redundant implementation for a one-shot HMAC-SHA512 hash computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * To be used together with hmac_hmac_sha512() to mitigate FI attacks. This
 * implementation is different to hmac_hmac_sha512() as it manually assembles
 * the HMAC functionality using SHA512. By using two different HMAC
 * implementations, injecting two identical faults affect different parts during
 * the HMAC compuation, which can be detected.
 *
 * @param key HMAC key.
 * @param msg Input message buffer.
 * @param[out] tag Authentication tag (`kHmacSha512DigestWords` bytes).
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_hmac_sha512_redundant(const hmac_key_t *key,
                                    const otcrypto_const_byte_buf_t *msg,
                                    otcrypto_word32_buf_t *tag);

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
 * @param key The key used for HMAC.
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha256_init(const hmac_key_t key, hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming HMAC-SHA384 computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key The key used for HMAC.
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha384_init(const hmac_key_t key, hmac_ctx_t *ctx);

/**
 * Initializes the context for a streaming HMAC-SHA512 computation.
 *
 * The key should be pre-processed into a buffer the size of a full message
 * block, according to FIPS 198-1, section 4.
 *
 * @param key The key used for HMAC.
 * @param[out] ctx Initialized context object.
 */
void hmac_hmac_sha512_init(const hmac_key_t key, hmac_ctx_t *ctx);

/**
 * Compute the checksum of an HMAC key.
 *
 * Call this routine after creating or modifying the HMAC key structure.
 *
 * @param key HMAC key.
 * @returns Checksum value.
 */
uint32_t hmac_key_integrity_checksum(const hmac_key_t *key);

/**
 * Perform an integrity check on the HMAC key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key HMAC key.
 * @returns Whether the integrity check passed.
 */
hardened_bool_t hmac_key_integrity_checksum_check(const hmac_key_t *key);

/**
 * Update the context with additional messsage data.
 *
 * This function can be used with all SHA2 and HMAC operations, and may be
 * called multiple times between init() and final().
 *
 * @param ctx Context object referring to a particular SHA-2/HMAC stream.
 * @param data Incoming message bytes buffer to be processed into the stream.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_update(hmac_ctx_t *ctx, const otcrypto_const_byte_buf_t *data);

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
status_t hmac_final(hmac_ctx_t *ctx, otcrypto_word32_buf_t *digest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_
