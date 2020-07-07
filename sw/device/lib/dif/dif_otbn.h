// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTBN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTBN_H_

#include "sw/device/lib/base/mmio.h"
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Configuration for initializing an OTBN device.
 */
typedef struct dif_otbn_config { mmio_region_t base_addr; } dif_otbn_config_t;

/**
 * Internal state of a OTBN device.
 *
 * Instances of this struct must be initialized by `dif_otbn_init()` before
 * being passed to other functions.
 */
typedef struct dif_otbn { mmio_region_t base_addr; } dif_otbn_t;

/**
 * Generic return codes for the functions in this library.
 */
typedef enum dif_otbn_result {
  /**
   * The function succeeded.
   */
  kDifOtbnOk,
  /**
   * The function failed a non-specific assertion.
   *
   * This error is not recoverable.
   */
  kDifOtbnError,
  /**
   * There is a problem with the argument(s) to the function.
   *
   * This return code is only returned before the function has any side effects.
   *
   * This error is recoverable and the operation can be retried after correcting
   * the problem with the argument(s).
   */
  kDifOtbnBadArg,

} dif_otbn_result_t;

/**
 * Initialize a OTBN device using `config` and return its internal state.
 *
 * A particular OTBN device must first be initialized by this function
 * before calling other functions of this library.
 *
 * @param config Configuration for initializing an OTBN device.
 * @param otbn OTBN instance that will store the internal state of the
 *             initialized OTBN device.
 * @return The result of the operation.
 */
dif_otbn_result_t dif_otbn_init(const dif_otbn_config_t *config,
                                dif_otbn_t *otbn);

/**
 * Reset OTBN device.
 *
 * Resets the given OTBN device by setting its configuration registers to
 * reset values. Disables interrupts, output, and input filter.
 *
 * @param otbn OTBN instance
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_reset(const dif_otbn_t *otbn);

/**
 * Start the execution of the application loaded into OTBN.
 *
 * @param otbn OTBN instance
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_start(const dif_otbn_t *otbn);

/**
 * Is OTBN busy executing an application?
 *
 * @param otbn OTBN instance
 * @param[out] busy OTBN is busy
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_is_busy(const dif_otbn_t *otbn, bool *busy);

// TODO: Think about making src/len in the imem/dmem write/read functions words
// instead of bytes. Easy for imem with 32b words, harder for dmem with WLEN
// words. And ideally, we have them consistent: either both are words, or none
// of them are words.

// TODO: We probably need more fine-granular error codes.

/**
 * Write an OTBN application into its instruction memory (IMEM)
 *
 * @param otbn OTBN instance
 * @param offset the byte offset in IMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len or size are invalid,
 * `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_imem_write(const dif_otbn_t *otbn, uint32_t offset,
                                      const void *src, size_t len);

/**
 * Read from OTBN's instruction memory (IMEM)
 *
 * @param otbn OTBN instance
 * @param offset the byte offset in IMEM the first word is read from
 * @param dest the main memory location to copy the data to (preallocated)
 * @param len number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len or size are invalid,
 * `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_imem_read(const dif_otbn_t *otbn, uint32_t offset,
                                     void *dest, size_t len);

/**
 * Write to OTBN's data memory (DMEM)
 *
 * @param otbn OTBN instance
 * @param offset the byte offset in DMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len or size are invalid,
 * `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn, uint32_t offset,
                                      const void *src, size_t len);

/**
 * Read from OTBN's data memory (DMEM)
 *
 * @param otbn OTBN instance
 * @param offset the byte offset in DMEM the first word is read from
 * @param dest the main memory location to copy the data to (preallocated)
 * @param len number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len or size are invalid,
 * `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn, uint32_t offset,
                                     void *dest, size_t len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTBN_H_
