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
  /* Digest size for SHA-256/HMAC-256 in bits, bytes and word respectively. */
  kHmacSha256DigestBits = 256,
  kHmacSha256DigestBytes = kHmacSha256DigestBits / 8,
  kHmacSha256DigestWords = kHmacSha256DigestBytes / sizeof(uint32_t),
  /* Digest size for SHA-384/HMAC-384 in bits, bytes and word respectively. */
  kHmacSha384DigestBits = 384,
  kHmacSha384DigestBytes = kHmacSha384DigestBits / 8,
  kHmacSha384DigestWords = kHmacSha384DigestBytes / sizeof(uint32_t),
  /* Digest size for SHA-512/HMAC-512 in bits, bytes and word respectively. */
  kHmacSha512DigestBits = 512,
  kHmacSha512DigestBytes = kHmacSha512DigestBits / 8,
  kHmacSha512DigestWords = kHmacSha512DigestBytes / sizeof(uint32_t),
  /* Internal block size for SHA-256/HMAC-256 in bits, bytes and word
     respectively. */
  kHmacSha256BlockBits = 2 * kHmacSha256DigestBits,
  kHmacSha256BlockBytes = kHmacSha256BlockBits / 8,
  kHmacSha256BlockWords = kHmacSha256BlockBytes / sizeof(uint32_t),
  /* Internal block size for SHA-384/512 and HMAC-384/512 in bits, bytes and
     word respectively. */
  kHmacSha512BlockBits = 2 * kHmacSha512DigestBits,
  kHmacSha512BlockBytes = kHmacSha512BlockBits / 8,
  kHmacSha512BlockWords = kHmacSha512BlockBytes / sizeof(uint32_t),
  /* Maximum digest size supported by HW natively in bits, bytes and words
     respectively. */
  kHmacMaxDigestBits = kHmacSha512DigestBits,
  kHmacMaxDigestBytes = kHmacMaxDigestBits / 8,
  kHmacMaxDigestWords = kHmacMaxDigestBytes / sizeof(uint32_t),
  /* Maximum internal block size bits, bytes and words respectively. */
  kHmacMaxBlockBits = kHmacSha512BlockBits,
  kHmacMaxBlockBytes = kHmacMaxBlockBits / 8,
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
  // key_wordlen == 0 is used to infer that this is SHA-2 operation.
  size_t key_wordlen;
  // The internal (message) block size of SHA-2 for this operation.
  size_t msg_block_bytelen;
  size_t digest_wordlen;
  // The following fields are saved and restored during streaming.
  uint32_t H[kHmacMaxDigestWords];
  uint32_t lower;
  uint32_t upper;
  // The following flags are used exclusively by the driver to determine whether
  // or not the driver needs to pass the incoming requests to HMAC HWIP.
  uint32_t hw_started;
  uint8_t partial_block[kHmacMaxBlockBytes];
  // The number of valid bytes in `partial_block`.
  size_t partial_block_len;
} hmac_ctx_t;

typedef enum hmac_mode {
  // SHA2-256
  kHmacModeSha256,
  // SHA2-384
  kHmacModeSha384,
  // SHA2-512
  kHmacModeSha512,
  // HMAC-256
  kHmacModeHmac256,
  // HMAC-384
  kHmacModeHmac384,
  // HMAC-512
  kHmacModeHmac512,
} hmac_mode_t;

/**
 * Initializes the context `ctx` according to given `hmac_mode` and `key`.
 *
 * This function does not invoke a HMAC HWIP operation, but instead prepares
 * `ctx` with necessary data for the streaming operations to be called later:
 *
 * i) Prepare CFG register value (with the exception of `sha_en` bit, #23014)
 * and store it into `ctx`. This value is repetitively loaded into HWIP during
 * future `hmac_update` and `hmac_final` calls.
 * ii) Copy given key and its length into `ctx` if the operation is HMAC.
 * iii) Initialize `hw_started` flag to false which indicates whether the very
 * first HWIP operation is executed or not. This helps decide whether start or
 * continue operation needs to be issues to HMAC HWIP later.
 * iv) Compute and store message block length and digest len fields to `ctx`.
 *
 * For SHA-2 operation, it must be that `key = NULL` and `key_wordlen = 0`.
 * For HMAC operations, `key` must point to a key buffer that contains the
 * processed key denoted as k0 in FIPS 198-1, Section 4. Therefore, the size of
 * the key must match the internal block size of the underlying hash function.
 * In other words, it means that:
 *   For HMAC-256, `key_wordlen = 64` with `key` referring to the value of k0,
 * which consists of exactly 64 words.
 *   For HMAC-384/512, `key_wordlen = 128`, with `key` referring to the value
 * of k0, which consists of exactly 128 words.
 *
 * @param[out] ctx Initialized context object for SHA2/HMAC-SHA2 operations.
 * @param hmac_mode Specifies the mode among SHA2-256/384/512, HMAC-256/384/512.
 * @param key Processed HMAC key.
 * @param key_wordlen The length of HMAC key, which must match the internal
 * block size of the underlying hash function.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_init(hmac_ctx_t *ctx, const hmac_mode_t hmac_mode,
                   const uint32_t *key, size_t key_wordlen);

/**
 * Updates the state of `ctx` with given additional messsage bytes.
 *
 * This function first checks whether incoming byte messages together with the
 * pending bytes `ctx->partial_block` are larger than the SHA-2/HMAC internal
 * block size implied by `ctx`.
 *
 * If the available message bytes are larger than the internal block size, then
 * the state of HWIP is restored from `ctx` and message bytes are fed into
 * MSG_FIFO in internal block granularity. When all blocks are processed, HWIP
 * is stopped and the state of HWIP is saved to `ctx`. The leftover message
 * bytes that are not sufficient to be a block are stored in `ctx-partial_block`
 * to be used in future `hmac_update` or `hmac_final` calls. Finally, the state
 * of HWIP is cleared.

 * If the available message bytes are smaller than a single internal block,
 * `ctx->partial_block` is appended with the incoming bytes and no HWIP
 * operation is issued.
 *
 * @param ctx Context object referring to a particular SHA-2/HMAC stream.
 * @param data Incoming message bytes to be processed into the stream.
 * @param len size of the `data` buffer in bytes.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_update(hmac_ctx_t *ctx, const uint8_t *data, size_t len);

/**
 * Finalize the SHA-2/HMAC stream and return digest/tag.
 *
 * This function works similar to `hmac_update`, in terms of how reamining
 * message bytes are handled, if there are any.
 *
 * First, the state of HWIP is restored. Then, any remaining message byte from
 * `ctx->partial_block` are fed to MSG_FIFO. At the end, process command is
 * invoked at HWIP to conclude SHA-2/HMAC operation and produce the digest/tag.
 * The result is read from HWIP into `digest` and the state of HWIP is cleared.
 *
 * `digest` should point to a sufficiently large buffer to accommodate
 * the resulting digest. `digest_wordlen` must match the digest length implied
 * by the mode used during the initialization of `ctx`, otherwise an error is
 * returned.
 *
 * @param ctx Context object referring to a particular stream.
 * @param[out] digest The digest value to be returned.
 * @param digest_wordlen The length of the digest in words.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t hmac_final(hmac_ctx_t *ctx, uint32_t *digest, size_t digest_wordlen);

/**
 * One-shot SHA-2/HMAC call.
 *
 * This function uses `hmac_mode` to determine whether to run SHA-2 or HMAC
 * including the digest size. See `hmac_mode_t` for possible values.
 *
 * For SHA-2 operation, it must be that `key = NULL` and `key_wordlen = 0`.
 * For HMAC operations, `key` must point to a key buffer that contains the
 * processed key denoted as k0 in FIPS 198-1, Section 4. Therefore, the size of
 * the key must match the internal block size of the underlying hash function.
 * In other words, it means that:
 *   For HMAC-256, `key_wordlen = 64` with `key` referring to the value of k0,
 * which consists of exactly 64 words.
 *   For HMAC-384/512, `key_wordlen = 128`, with `key` referring to the value
 * of k0, which consists of exactly 128 words.
 *
 * `digest` should point to a sufficiently large buffer to accommodate
 * the resulting digest. `digest_wordlen` must match the digest length implied
 * by the mode used during the initialization of `ctx`, otherwise an error is
 * returned.
 *
 * @param[out] ctx Initialized context object for SHA2/HMAC-SHA2 operations.
 * @param hmac_mode Specifies the mode among SHA2-256/384/512, HMAC-256/384/512.
 * @param key Processed HMAC key.
 * @param key_wordlen The length of HMAC key, which must match the internal
 * block size of the underlying hash function.
 * @param[out] digest The digest value to be returned.
 * @param digest_wordlen The length of the digest in words.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t hmac(const hmac_mode_t hmac_mode, const uint32_t *key,
              size_t key_wordlen, const uint8_t *data, size_t len,
              uint32_t *digest, size_t digest_wordlen);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_
