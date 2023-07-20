// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_HMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_HMAC_H_

/**
 * @file
 * @brief <a href="/hw/ip/hmac/doc/">HMAC</a> Device Interface Functions
 */

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_hmac_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Supported HMAC modes of operation.
 */
typedef enum dif_hmac_mode {
  /** The HMAC mode. */
  kDifHmacModeHmac = 0,
  /** The SHA256-only mode. */
  kDifHmacModeSha256,
} dif_hmac_mode_t;

/**
 * Supported byte endienness options.
 */
typedef enum dif_hmac_endianness {
  /** Big endian byte ordering. */
  kDifHmacEndiannessBig = 0,
  /** Little endian byte ordering. */
  kDifHmacEndiannessLittle,
} dif_hmac_endianness_t;

/**
 * Configuration for a single HMAC Transaction
 */
typedef struct dif_hmac_transaction {
  /** Byte endianness for writes to the FIFO. */
  dif_hmac_endianness_t message_endianness;
  /** Byte endianness for reads from the digest. */
  dif_hmac_endianness_t digest_endianness;
} dif_hmac_transaction_t;

/**
 * A typed representation of the HMAC digest.
 */
typedef struct dif_hmac_digest {
  uint32_t digest[8];
} dif_hmac_digest_t;

/**
 * Resets the HMAC engine and readies it to receive a new message to process an
 * HMAC digest.
 *
 * This function causes the HMAC engine to start its operation. After a
 * successful call to this function, |dif_hmac_fifo_push()| can be called to
 * write the message for HMAC processing.
 *
 * This function must be called with a valid `key` that references a 32-byte,
 * contiguous, readable region where the key may be copied from.
 *
 * @param hmac The HMAC device to start HMAC operation for.
 * @param key The 256-bit HMAC key.
 * @param config The per-transaction configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_mode_hmac_start(const dif_hmac_t *hmac,
                                      const uint8_t *key,
                                      const dif_hmac_transaction_t config);

/**
 * Resets the HMAC engine and readies it to receive a new message to process a
 * SHA256 digest.
 *
 * This function causes the HMAC engine to start its operation. After a
 * successful call to this function, |dif_hmac_fifo_push()| can be called to
 * write the message for SHA256 processing.
 *
 * @param hmac The HMAC device to start SHA256 operation for.
 * @param config The per-transaction configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_mode_sha256_start(const dif_hmac_t *hmac,
                                        const dif_hmac_transaction_t config);

/**
 * Attempts to send `len` bytes from the buffer pointed to by `data` to the
 * device described by `hmac`. This function will send to the message FIFO until
 * the FIFO fills up or `len` bytes have been sent.
 *
 * In the event that the FIFO fills up before `len` bytes have been sent this
 * function will return a `kDifHmacFifoFull` error. In this case it is valid
 * to call this function again by advancing `data` by `len` - |*bytes_sent|
 * bytes. It may be desirable to wait for space to free up on the FIFO before
 * issuing subsequent calls to this function, but it is not strictly
 * necessary. The number of entries in the FIFO can be queried with
 * `dif_hmac_fifo_count_entries()`.
 *
 * `data` *must* point to an allocated buffer of at least length `len`.
 *
 * @param hmac The HMAC device to send to.
 * @param data A contiguous buffer to copy from.
 * @param len The length of the buffer to copy from.
 * @param[out] bytes_sent The number of bytes sent to the FIFO (optional).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_fifo_push(const dif_hmac_t *hmac, const void *data,
                                size_t len, size_t *bytes_sent);

/**
 * Retrieves the number of entries in the HMAC FIFO. These entries may be
 * semi-arbitrary in length; this function should not be used to calculate
 * message length.
 *
 * @param hmac The HMAC device to get the FIFO depth for.
 * @param[out] num_entries The number of entries in the FIFO.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_fifo_count_entries(const dif_hmac_t *hmac,
                                         uint32_t *num_entries);

/**
 * Retrieves the number of bits in the loaded HMAC device.
 * `dif_hmac_fifo_count_entries()` should be called before this function to
 * ensure the FIFO is empty, as any bits in the FIFO are not counted in
 * `msg_len`.
 *
 * @param hmac The HMAC device to get the message length for.
 * @param[out] msg_len The number of bits in the HMAC message.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_get_message_length(const dif_hmac_t *hmac,
                                         uint64_t *msg_len);

/**
 * Attempts to run HMAC or SHA256 depending on the mode `hmac` was initialized
 * in. Calls to this function always succeed and return without blocking. The
 * caller can use `dif_hmac_check_state()` to check for errors and for the
 * `DIF_HMAC_DONE` status before reading the digest with
 * `dif_hmac_digest_read()`.
 *
 * @param hmac The HMAC device to initiate the run on.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_process(const dif_hmac_t *hmac);

/**
 * Attempts to finish a transaction started with `dif_hmac_mode_*_start`, and
 * reads the final digest in the buffer referenced by `digest`.
 *
 * This queries the `INTR_STATE` register to check if the HMAC is finished, and
 * will acknowledge a `hmac_done` interrupt. If that register is not pending,
 * then this function assumes HMAC is still processing and will return
 * `kDifHmacErrorDigestProcessing`.
 *
 * Once the digest has been read, the HMAC and SHA256 datapaths are disabled,
 * clearing the digest registers.
 *
 * `digest` must reference an allocated, contiguous, 32-byte buffer. This buffer
 * shall also be 4-byte aligned. This is all consistent with the platform
 * requirements for size and alignment requirements of `dif_hmac_digest_t`.
 *
 * @param hmac The HMAC device to read the digest from.
 * @param[out] digest A contiguous 32-byte, 4-byte aligned buffer for the
 * digest.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_finish(const dif_hmac_t *hmac, dif_hmac_digest_t *digest);

/**
 * Randomizes internal secret registers on the HMAC device. This includes the
 * key, hash value, and internal state machine. The value of `entropy` will be
 * used to "randomize" the internal state of the HMAC device. See the HMAC IP
 * documentation for more information: hw/ip/hmac/doc.
 *
 * @param hmac The HMAC device to clobber state on.
 * @param entropy A source of randomness to write to the HMAC internal state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_hmac_wipe_secret(const dif_hmac_t *hmac, uint32_t entropy);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_HMAC_H_
