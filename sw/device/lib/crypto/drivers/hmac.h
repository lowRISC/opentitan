// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /* Number of bits in an HMAC or SHA-256 digest. */
  kHmacDigestNumBits = 256,
  /* Number of bytes in an HMAC or SHA-256 digest. */
  kHmacDigestNumBytes = kHmacDigestNumBits / 8,
  /* Number of words in an HMAC or SHA-256 digest. */
  kHmacDigestNumWords = kHmacDigestNumBytes / sizeof(uint32_t),
  /* Number of bits in an HMAC key. */
  kHmacKeyNumBits = 256,
  /* Number of bytes in an HMAC key. */
  kHmacKeyNumBytes = kHmacKeyNumBits / 8,
  /* Number of words in an HMAC key. */
  kHmacKeyNumWords = kHmacKeyNumBytes / sizeof(uint32_t),
};

/**
 * A typed representation of the HMAC or SHA256 digest.
 */
typedef struct hmac_digest {
  uint32_t digest[kHmacDigestNumWords];
} hmac_digest_t;

/**
 * A typed representation of an HMAC key.
 */
typedef struct hmac_key {
  uint32_t key[kHmacKeyNumWords];
} hmac_key_t;

/**
 * Initializes the HMAC block in SHA256 mode.
 *
 * If the HMAC block is non-idle, calling this function aborts the previous
 * operation.
 *
 * This function resets the HMAC module to clear the digest register.
 * It then configures the HMAC block in SHA256 mode with little endian
 * data input and digest output.
 */
void hmac_sha256_init(void);

/**
 * Initializes the HMAC block in HMAC mode.
 *
 * If the HMAC block is non-idle, calling this function aborts the previous
 * operation.
 *
 * This function resets the HMAC module to clear the digest register.
 * It then configures the HMAC block in SHA256 mode with little endian
 * data input and digest output.
 *
 * @param key HMAC key.
 */
void hmac_hmac_init(const hmac_key_t *key);

/**
 * Sends `len` bytes from `data` to the HMAC or SHA2-256 function.
 *
 * This function does not check for the size of the available HMAC
 * FIFO. Since the this function is meant to run in blocking mode,
 * polling for FIFO status is equivalent to stalling on FIFO write.
 *
 * @param data Buffer to copy data from.
 * @param len size of the `data` buffer in bytes.
 */
void hmac_update(const uint8_t *data, size_t len);

/**
 * Finalizes HMAC or SHA256 operation and writes `digest` buffer.
 *
 * Blocks while the device is processing. Clears the hardware digest registers
 * and configuration when done.
 *
 * @param[out] digest Buffer to copy digest to.
 */
void hmac_final(hmac_digest_t *digest);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_HMAC_H_
