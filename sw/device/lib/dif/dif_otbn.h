// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTBN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTBN_H_

/**
 * @file
 * @brief <a href="/hw/ip/otbn/doc/">OTBN</a> Device Interface Functions
 */

#include <stddef.h>
#include <stdint.h>
#include "sw/device/lib/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Configuration for initializing an OTBN device.
 */
typedef struct dif_otbn_config {
  /** Base address of the OTBN device in the system. */
  mmio_region_t base_addr;
} dif_otbn_config_t;

/**
 * Internal state of a OTBN device.
 *
 * Instances of this struct must be initialized by `dif_otbn_init()` before
 * being passed to other functions.
 */
typedef struct dif_otbn {
  /** Base address of the OTBN device in the system. */
  mmio_region_t base_addr;
} dif_otbn_t;

/**
 * Generic return codes for the functions in the OTBN DIF library.
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
  kDifOtbnBadArg
} dif_otbn_result_t;

/**
 * OTBN Errors
 *
 * OTBN uses a bitfield to indicate which errors have been seen. Multiple errors
 * can be seen at the same time. This enum gives the individual bits that may be
 * set for different errors.
 */
typedef enum dif_otbn_err_bits {
  kDifOtbnErrBitsNoError = 0,
  /** Load or store to invalid address. */
  kDifOtbnErrBitsBadDataAddr = (1 << 0),
  /** Instruction fetch from invalid address. */
  kDifOtbnErrBitsBadInsnAddr = (1 << 1),
  /** Call stack underflow or overflow. */
  kDifOtbnErrBitsCallStack = (1 << 2),
  /** Illegal instruction execution attempted */
  kDifOtbnErrBitsIllegalInsn = (1 << 3),
  /** LOOP[I] related error */
  kDifOtbnErrBitsLoop = (1 << 4),
  /** Error seen in Imem read */
  kDifOtbnErrBitsFatalImem = (1 << 5),
  /** Error seen in Dmem read */
  kDifOtbnErrBitsFatalDmem = (1 << 6),
  /** Error seen in RF read */
  kDifOtbnErrBitsFatalReg = (1 << 7)
} dif_otbn_err_bits_t;

/**
 * OTBN interrupt configuration.
 *
 * Enumeration used to enable, disable, test and query the OTBN interrupts.
 * Please see the comportability specification for more information:
 * https://docs.opentitan.org/doc/rm/comportability_specification/
 */
typedef enum dif_otbn_interrupt {
  /**
   * OTBN is done, it has run the application to completion.
   *
   * Associated with the `otbn.INTR_STATE.done` hardware interrupt.
   */
  kDifOtbnInterruptDone = 0,

} dif_otbn_interrupt_t;

/**
 * Generic enable/disable enumeration.
 *
 * Enumeration used to enable/disable bits, flags, ...
 */
typedef enum dif_otbn_enable {
  /** Enable functionality. */
  kDifOtbnEnable = 0,
  /** Disable functionality. */
  kDifOtbnDisable,
} dif_otbn_enable_t;

/**
 * Initialize a OTBN device using `config` and return its internal state.
 *
 * A particular OTBN device must first be initialized by this function
 * before calling other functions of this library.
 *
 * @param config Configuration for initializing an OTBN device.
 * @param[out] otbn OTBN instance that will store the internal state of the
 *             initialized OTBN device.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
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
 * OTBN get requested IRQ state.
 *
 * Get the state of the requested IRQ in `irq_type`.
 *
 * @param otbn OTBN state data.
 * @param irq_type IRQ to get the state of.
 * @param[out] state IRQ state.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_irq_state_get(const dif_otbn_t *otbn,
                                         dif_otbn_interrupt_t irq_type,
                                         dif_otbn_enable_t *state);

/**
 * OTBN clear requested IRQ state.
 *
 * Clear the state of the requested IRQ in `irq_type`. Primary use of this
 * function is to de-assert the interrupt after it has been serviced.
 *
 * @param otbn OTBN state data.
 * @param irq_type IRQ to be de-asserted.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_irq_state_clear(const dif_otbn_t *otbn,
                                           dif_otbn_interrupt_t irq_type);

/**
 * OTBN disable interrupts.
 *
 * Disable generation of all OTBN interrupts, and pass previous interrupt state
 * in `state` back to the caller. Parameter `state` is ignored if NULL.
 *
 * @param otbn OTBN state data.
 * @param[out] state IRQ state for use with `dif_otbn_irqs_restore`.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_irqs_disable(const dif_otbn_t *otbn,
                                        uint32_t *state);

/**
 * OTBN restore IRQ state.
 *
 * Restore previous OTBN IRQ state. This function is used to restore the
 * OTBN interrupt state prior to `dif_otbn_irqs_disable` function call.
 *
 * @param otbn OTBN instance
 * @param state IRQ state to restore.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_irqs_restore(const dif_otbn_t *otbn, uint32_t state);

/**
 * OTBN interrupt control.
 *
 * Enable/disable an OTBN interrupt specified in `irq_type`.
 *
 * @param otbn OTBN instance
 * @param irq_type OTBN interrupt type.
 * @param enable enable or disable the interrupt.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL`, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_irq_control(const dif_otbn_t *otbn,
                                       dif_otbn_interrupt_t irq_type,
                                       dif_otbn_enable_t enable);

/**
 * OTBN interrupt force.
 *
 * Force interrupt specified in `irq_type`.
 *
 * @param otbn OTBN instance
 * @param irq_type OTBN interrupt type to be forced.
 * @return `dif_otbn_result_t`.
 */
dif_otbn_result_t dif_otbn_irq_force(const dif_otbn_t *otbn,
                                     dif_otbn_interrupt_t irq_type);

/**
 * Start the execution of the application loaded into OTBN at the start address.
 *
 * @param otbn OTBN instance
 * @param start_addr The IMEM byte address to start the execution at.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or `start_addr` is invalid,
 *         `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_start(const dif_otbn_t *otbn,
                                 unsigned int start_addr);

/**
 * Is OTBN busy executing an application?
 *
 * @param otbn OTBN instance
 * @param[out] busy OTBN is busy
 * @return `kDifOtbnBadArg` if `otbn` or `busy` is `NULL`,
 *         `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_is_busy(const dif_otbn_t *otbn, bool *busy);

/**
 * Get the error bits set by the device if the operation failed.
 *
 * @param otbn OTBN instance
 * @param[out] err_bits The error bits returned by the hardware.
 * @return `kDifOtbnBadArg` if `otbn` or `err_code` is `NULL`,
 *         `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_get_err_bits(const dif_otbn_t *otbn,
                                        dif_otbn_err_bits_t *err_bits);

/**
 * Write an OTBN application into its instruction memory (IMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in IMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len_bytes number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len_bytes or size are
 * invalid, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_imem_write(const dif_otbn_t *otbn,
                                      uint32_t offset_bytes, const void *src,
                                      size_t len_bytes);

/**
 * Read from OTBN's instruction memory (IMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in IMEM the first word is read from
 * @param[out] dest the main memory location to copy the data to (preallocated)
 * @param len_bytes number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len_bytes or size are
 * invalid, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_imem_read(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, void *dest,
                                     size_t len_bytes);

/**
 * Write to OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in DMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len_bytes number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len_bytes or size are
 * invalid, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn,
                                      uint32_t offset_bytes, const void *src,
                                      size_t len_bytes);

/**
 * Read from OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in DMEM the first word is read from
 * @param[out] dest the main memory location to copy the data to (preallocated)
 * @param len_bytes number of bytes to copy.
 * @return `kDifOtbnBadArg` if `otbn` is `NULL` or len_bytes or size are
 * invalid, `kDifOtbnOk` otherwise.
 */
dif_otbn_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, void *dest,
                                     size_t len_bytes);

/**
 * Get the size of OTBN's data memory in bytes.
 *
 * @param otbn OTBN instance
 * @return data memory size in bytes
 */
size_t dif_otbn_get_dmem_size_bytes(const dif_otbn_t *otbn);

/**
 * Get the size of OTBN's instruction memory in bytes.
 *
 * @param otbn OTBN instance
 * @return instruction memory size in bytes
 */
size_t dif_otbn_get_imem_size_bytes(const dif_otbn_t *otbn);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_OTBN_H_
