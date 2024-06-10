// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_HMAC_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_HMAC_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Size of a SHA-256 digest in bytes.
   */
  kHmacDigestNumBytes = 32,
  /**
   * Size of a SHA-256 digest in 32-bit words.
   */
  kHmacDigestNumWords = kHmacDigestNumBytes / sizeof(uint32_t),
};

/**
 * A typed representation of the HMAC digest.
 */
typedef struct hmac_digest {
  uint32_t digest[kHmacDigestNumWords];
} hmac_digest_t;

/**
 * Configure the HMAC block in SHA256 mode.
 *
 * This function resets the HMAC module to clear the digest register.
 * It then configures the HMAC block in SHA256 mode with digest output
 * in the requested endianness.
 *
 * @param big_endian Whether or not to initialize the peripheral for big-endian
 *                   results.
 */
void hmac_sha256_configure(bool big_endian_digest);

/**
 * Starts a new operation on the pre-configured HMAC block.
 *
 * Call `hmac_sha256_configure` first.
 */
void hmac_sha256_start(void);

/**
 * Configures and starts HMAC in SHA256 mode with little-endian output.
 */
inline void hmac_sha256_init(void) {
  hmac_sha256_configure(false);
  hmac_sha256_start();
}

/**
 * Sends `len` bytes from `data` to the SHA2-256 function.
 *
 * This function does not check for the size of the available HMAC
 * FIFO. Since the this function is meant to run in blocking mode,
 * polling for FIFO status is equivalent to stalling on FIFO write.
 *
 * @param data Buffer to copy data from.
 * @param len Size of the `data` buffer in bytes.
 */
void hmac_sha256_update(const void *data, size_t len);

/**
 * Sends `len` 32-bit words from `data` to the SHA2-256 function.
 *
 * This function does not check for the size of the available HMAC
 * FIFO. Since the this function is meant to run in blocking mode,
 * polling for FIFO status is equivalent to stalling on FIFO write.
 *
 * @param data Buffer to copy data from.
 * @param len Size of the `data` buffer in words.
 */
void hmac_sha256_update_words(const uint32_t *data, size_t len);

/**
 * Begin processing the final digest for HMAC.
 */
void hmac_sha256_process(void);

/**
 * Finalizes SHA256 operation and copies truncated output.
 *
 * Copies only the first `len` 32-bit words of the digest. The caller must
 * ensure enough space is available in the buffer.
 *
 * @param[out] digest Buffer to copy digest to.
 * @param[out] len Requested word-length.
 */
void hmac_sha256_final_truncated(uint32_t *digest, size_t len);

/**
 * Finalizes SHA256 operation and writes `digest` buffer.
 *
 * @param[out] digest Buffer to copy digest to.
 */
inline void hmac_sha256_final(hmac_digest_t *digest) {
  hmac_sha256_final_truncated(digest->digest, ARRAYSIZE(digest->digest));
}

/**
 * Convenience function for computing the SHA-256 digest of a contiguous buffer.
 *
 * @param data Buffer to copy data from.
 * @param len Size of the `data` buffer in bytes.
 * @param[out] digest Buffer to copy digest to.
 */
void hmac_sha256(const void *data, size_t len, hmac_digest_t *digest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_HMAC_H_
