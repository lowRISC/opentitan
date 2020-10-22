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
#include "sw/device/lib/base/mmio.h"

/**
 * HMAC interrupt configuration.
 *
 * Enumeration used to enable, disable, test and query the HMAC interrupts.
 * Please see the comportability specification for more information:
 * https://docs.opentitan.org/doc/rm/comportability_specification/
 */
typedef enum dif_hmac_interrupt {
  /**
   * HMAC is done.
   *
   * Associated with the `hmac.INTR_STATE.hmac_done` hardware interrupt.
   */
  kDifHmacInterruptHmacDone = 0,

  /**
   * FIFO empty.
   *
   * Associated with the `hmac.INTR_STATE.fifo_empty` hardware interrupt.
   */
  kDifHmacInterruptFifoEmpty,

  /**
   * HMAC error occurred.
   *
   * Associated with the `hmac.INTR_STATE.hmac_err` hardware interrupt.
   */
  kDifHmacInterruptHmacErr,
} dif_hmac_interrupt_t;

/**
 * Generic enable/disable enumeration.
 *
 * Enumeration used to enable/disable bits, flags, ...
 */
typedef enum dif_hmac_enable {
  /** Enable interrupt. */
  kDifHmacEnable = 0,
  /** Disable interrupt. */
  kDifHmacDisable,
} dif_hmac_enable_t;

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
 * Error codes for HMAC functions that may exhibit generic failures.
 */
typedef enum dif_hmac_result {
  /** No error occurred. */
  kDifHmacOk = 0,
  /** An unknown error occurred. */
  kDifHmacError,
  /** An invalid argument was provided. */
  kDifHmacBadArg,
} dif_hmac_result_t;

/**
 * Error codes for HMAC FIFO operations that may fail.
 */
typedef enum dif_hmac_fifo_result {
  /** No error occurred. */
  kDifHmacFifoOk = 0,
  /** An unknown error occurred. */
  kDifHmacFifoError,
  /** An invalid argument was provided. */
  kDifHmacFifoBadArg,
  /**
   * The FIFO filled up before the buffer was fully consumed.
   *
   * Retryable. This error indicates that FIFO has filled up and will empty over
   * time. A function that returns this error may be retried at any time, or the
   * caller may choose to do so when the `kDifHmacInterruptFifoEmpty` interrupt
   * is raised, provided this interrupt has been enabled via the interrupt API.
   */
  kDifHmacFifoFull,
} dif_hmac_fifo_result_t;

/**
 * Error codes for reading the HMAC digest.
 */
typedef enum dif_hmac_digest_result {
  /** No error occurred. */
  kDifHmacDigestOk = 0,
  /** An unknown error occurred. */
  kDifHmacDigestError,
  /** An invalid argument was provided. */
  kDifHmacDigestBadArg,
  /**
   * The HMAC operation is still in progress.
   *
   * Retryable. This error indicates HMAC is still processing and will finish in
   * time. A function that returns this error may be retried at any time, or the
   *  caller may choose to do so when the `kDifHmacInterruptHmacDone` interrupt
   *  is raised, provided this interrupt has been enabled via the interrupt API.
   *
   *  Any function that returns this error is guaranteed to have not produced
   *  any side effects.
   */
  kDifHmacDigestProcessing,
} dif_hmac_digest_result_t;

/**
 * Configuration for initializing the HMAC device.
 */
typedef struct dif_hmac_config {
  /** The base address for registers in the HMAC IP. */
  mmio_region_t base_addr;
  /** Byte endianness for writes to the FIFO. */
  dif_hmac_endianness_t message_endianness;
  /** Byte endianness for reads from the digest. */
  dif_hmac_endianness_t digest_endianness;
} dif_hmac_config_t;

/**
 * A typed representation of the HMAC digest.
 */
typedef struct dif_hmac_digest { uint32_t digest[8]; } dif_hmac_digest_t;

/**
 * State for a particular HMAC device.
 *
 * Its member variables should be considered private, and are only provided so
 * that callers can allocate it.
 */
typedef struct dif_hmac { mmio_region_t base_addr; } dif_hmac_t;

/**
 * Initializes the HMAC device described by `config`, writing internal state to
 * `hmac_out`.
 *
 * This function *must* be called on a particular `mmio_region_t` before calling
 * any other functions in this header with that `mmio_region_t`.
 *
 * @param config Configuration supplied for initializing a particular device.
 * @param[out] hmac_out The location at which to write HMAC state. This location
 *                 must be valid to write to.
 * @return `kDifHmacBadArg` if `config` is null or contains illegal
 *          arguments or `hmac_out` is null, `kDifHmacOk` otherwise.
 */
dif_hmac_result_t dif_hmac_init(const dif_hmac_config_t *config,
                                dif_hmac_t *hmac_out);

/**
 * HMAC get requested IRQ state.
 *
 * Get the state of the requested IRQ in `irq_type`.
 *
 * @param hmac HMAC state data.
 * @param irq_type IRQ to get the state of.
 * @param[out] state IRQ state passed back to the caller.
 * @return `dif_hmac_result_t`.
 */
dif_hmac_result_t dif_hmac_irq_state_get(const dif_hmac_t *hmac,
                                         dif_hmac_interrupt_t irq_type,
                                         dif_hmac_enable_t *state);
/**
 * HMAC clear requested IRQ state.
 *
 * Clear the state of the requested IRQ in `irq_type`. Primary use of this
 * function is to de-assert the interrupt after it has been serviced.
 *
 * @param hmac HMAC state data.
 * @param irq_type IRQ to be de-asserted.
 * @return `dif_hmac_result_t`.
 */
dif_hmac_result_t dif_hmac_irq_state_clear(const dif_hmac_t *hmac,
                                           dif_hmac_interrupt_t irq_type);

/**
 * HMAC disable interrupts.
 *
 * Disable generation of all HMAC interrupts, and pass previous interrupt state
 * in `state` back to the caller. Parameter `state` is ignored if NULL.
 *
 * @param hmac HMAC state data.
 * @param[out] state IRQ state passed back to the caller.
 * @return 'dif_hmac_result_t'.
 */
dif_hmac_result_t dif_hmac_irqs_disable(const dif_hmac_t *hmac,
                                        uint32_t *state);

/**
 * HMAC restore IRQ state.
 *
 * Restore previous HMAC IRQ state. This function is used to restore the
 * HMAC interrupt state prior to `dif_hmac_irqs_disable` function call.
 *
 * @param hmac HMAC state data.
 * @param state IRQ state to restore.
 * @return 'dif_hmac_result_t'.
 */
dif_hmac_result_t dif_hmac_irqs_restore(const dif_hmac_t *hmac, uint32_t state);

/**
 * HMAC interrupt control.
 *
 * Enable/disable an HMAC interrupt specified in `irq_type`.
 *
 * @param hmac HMAC state data.
 * @param irq_type HMAC interrupt type.
 * @param enable enable or disable the interrupt.
 * @return `dif_hmac_result_t`.
 */
dif_hmac_result_t dif_hmac_irq_control(const dif_hmac_t *hmac,
                                       dif_hmac_interrupt_t irq_type,
                                       dif_hmac_enable_t enable);

/**
 * HMAC interrupt force.
 *
 * Force interrupt specified in `irq_type`.
 *
 * @param hmac HMAC state data.
 * @param irq_type HMAC interrupt type to be forced.
 * @return `dif_hmac_result_t`.
 */
dif_hmac_result_t dif_hmac_irq_force(const dif_hmac_t *hmac,
                                     dif_hmac_interrupt_t irq_type);

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
 * @return `kDifHmacBadArg` if `hmac` or `key` is null, `kDifHmacOk` otherwise.
 */
dif_hmac_result_t dif_hmac_mode_hmac_start(const dif_hmac_t *hmac,
                                           const uint8_t *key);

/**
 * Resets the HMAC engine and readies it to receive a new message to process a
 * SHA256 digest.
 *
 * This function causes the HMAC engine to start its operation. After a
 * successful call to this function, |dif_hmac_fifo_push()| can be called to
 * write the message for SHA256 processing.
 *
 * @param hmac The HMAC device to start SHA256 operation for.
 * @return `kDifHmacBadArg` if `hmac` null, `kDifHmacOk` otherwise.
 */
dif_hmac_result_t dif_hmac_mode_sha256_start(const dif_hmac_t *hmac);

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
 * @return `kDifHmacFifoFull` if the FIFO fills up, `kDifHmacFifoBadArg` if
 *         `hmac` or `data` is null, and `kDifHmacFifoOk` otherwise.
 */
dif_hmac_fifo_result_t dif_hmac_fifo_push(const dif_hmac_t *hmac,
                                          const void *data, size_t len,
                                          size_t *bytes_sent);

/**
 * Retrieves the number of entries in the HMAC FIFO. These entries may be
 * semi-arbitrary in length; this function should not be used to calculate
 * message length.
 *
 * @param hmac The HMAC device to get the FIFO depth for.
 * @param[out] num_entries The number of entries in the FIFO.
 * @return `kDifHmacBadArg` if `hmac` or `num_entries` is null, `kDifHmacOk`
 *         otherwise.
 */
dif_hmac_result_t dif_hmac_fifo_count_entries(const dif_hmac_t *hmac,
                                              uint32_t *num_entries);

/**
 * Retrieves the number of bits in the loaded HMAC device.
 * `dif_hmac_fifo_count_entries()` should be called before this function to
 * ensure the FIFO is empty, as any bits in the FIFO are not counted in
 * `msg_len`.
 *
 * @param hmac The HMAC device to get the message length for.
 * @param[out] msg_len The number of bits in the HMAC message.
 * @return `kDifHmacBadArg` if `hmac` or `msg_len` is null, `kDifHmacOk`
 *         otherwise.
 */
dif_hmac_result_t dif_hmac_get_message_length(const dif_hmac_t *hmac,
                                              uint64_t *msg_len);

/**
 * Attempts to run HMAC or SHA256 depending on the mode `hmac` was initialized
 * in. Calls to this function always succeed and return without blocking. The
 * caller can use `dif_hmac_check_state()` to check for errors and for the
 * `DIF_HMAC_DONE` status before reading the digest with
 * `dif_hmac_digest_read()`.
 *
 * @param hmac The HMAC device to initiate the run on.
 * @return `kDifHmacBadArg` if `hmac` is null `kDifHmacOk` otherwise.
 */
dif_hmac_result_t dif_hmac_process(const dif_hmac_t *hmac);

/**
 * Attempts to read the HMAC digest and store store the result in the buffer
 * referenced by `digest`.
 *
 * If HMAC is still processing this will return `kDifHmacErrorDigestProcessing`
 *
 * `digest` must reference an allocated, contiguous, 32-byte buffer. This buffer
 * shall also be 4-byte aligned. This is all consistent with the platform
 * requirements for size and alignment requirements of `dif_hmac_digest_t`.
 *
 * @param hmac The HMAC device to read the digest from.
 * @param[out] digest A contiguous 32-byte, 4-byte aligned buffer for the
 * digest.
 * @return `kDifHmacBadArg` if `hmac` or `digest` is null,
 *         `kDifHmacDigestProcessing` if HMAC is still processing, and
 *         `kDifHmacOk` otherwise.
 */
dif_hmac_digest_result_t dif_hmac_digest_read(const dif_hmac_t *hmac,
                                              dif_hmac_digest_t *digest);

/**
 * Randomizes internal secret registers on the HMAC device. This includes the
 * key, hash value, and internal state machine. The value of `entropy` will be
 * used to "randomize" the internal state of the HMAC device. See the HMAC IP
 * documentation for more information: hw/ip/hmac/doc.
 *
 * @param hmac The HMAC device to clobber state on.
 * @param entropy A source of randomness to write to the HMAC internal state.
 * @return `kDifHmacBadArg` if `hmac` is null `kDifHmacOk` otherwise.
 */
dif_hmac_result_t dif_hmac_wipe_secret(const dif_hmac_t *hmac,
                                       uint32_t entropy);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_HMAC_H_
