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
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_otbn_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * OTBN commands
 */
typedef enum dif_otbn_cmd {
  kDifOtbnCmdExecute = 0x01,
  kDifOtbnCmdSecWipeDmem = 0x02,
  kDifOtbnCmdSecWipeImem = 0x03,
} dif_otbn_cmd_t;

/**
 * OTBN status
 */
typedef enum dif_otbn_status {
  kDifOtbnStatusIdle = 0x00,
  kDifOtbnStatusBusyExecute = 0x01,
  kDifOtbnStatusBusySecWipeDmem = 0x02,
  kDifOtbnStatusBusySecWipeImem = 0x03,
  kDifOtbnStatusLocked = 0xFF,
} dif_otbn_status_t;

/**
 * OTBN Errors
 *
 * OTBN uses a bitfield to indicate which errors have been seen. Multiple errors
 * can be seen at the same time. This enum gives the individual bits that may be
 * set for different errors.
 */
typedef enum dif_otbn_err_bits {
  kDifOtbnErrBitsNoError = 0,
  /** A BAD_DATA_ADDR error was observed. */
  kDifOtbnErrBitsBadDataAddr = (1 << 0),
  /** A BAD_INSN_ADDR error was observed. */
  kDifOtbnErrBitsBadInsnAddr = (1 << 1),
  /** A CALL_STACK error was observed. */
  kDifOtbnErrBitsCallStack = (1 << 2),
  /** An ILLEGAL_INSN error was observed. */
  kDifOtbnErrBitsIllegalInsn = (1 << 3),
  /** A LOOP error was observed. */
  kDifOtbnErrBitsLoop = (1 << 4),
  /** A IMEM_INTG_VIOLATION error was observed. */
  kDifOtbnErrBitsImemIntgViolation = (1 << 16),
  /** A DMEM_INTG_VIOLATION error was observed. */
  kDifOtbnErrBitsDmemIntgViolation = (1 << 17),
  /** A REG_INTG_VIOLATION error was observed. */
  kDifOtbnErrBitsRegIntgViolation = (1 << 18),
  /** A BUS_INTG_VIOLATION error was observed. */
  kDifOtbnErrBitsBusIntgViolation = (1 << 19),
  /** An ILLEGAL_BUS_ACCESS error was observed. */
  kDifOtbnErrBitsIllegalBusAccess = (1 << 20),
  /** A LIFECYCLE_ESCALATION error was observed. */
  kDifOtbnErrBitsLifecycleEscalation = (1 << 21),
  /** A FATAL_SOFTWARE error was observed. */
  kDifOtbnErrBitsFatalSoftware = (1 << 22),
} dif_otbn_err_bits_t;

/**
 * Initialize a OTBN device using `config` and return its internal state.
 *
 * A particular OTBN device must first be initialized by this function
 * before calling other functions of this library.
 *
 * @param base_addr Hardware instantiation base address.
 * @param[out] otbn OTBN instance that will store the internal state of the
 *             initialized OTBN device.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_init(mmio_region_t base_addr, dif_otbn_t *otbn);

/**
 * Reset OTBN device.
 *
 * Resets the given OTBN device by setting its configuration registers to
 * reset values. Disables interrupts, output, and input filter.
 *
 * @param otbn OTBN instance
 * @return The result of the operation.
 */
dif_result_t dif_otbn_reset(const dif_otbn_t *otbn);

/**
 * Start an operation by issuing a command.
 *
 * @param otbn OTBN instance.
 * @param cmd The command.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_write_cmd(const dif_otbn_t *otbn, dif_otbn_cmd_t cmd);

/**
 * Gets the current status of OTBN.
 *
 * @param otbn OTBN instance
 * @param[out] status OTBN status
 * @return The result of the operation.
 */
dif_result_t dif_otbn_get_status(const dif_otbn_t *otbn,
                                 dif_otbn_status_t *status);

/**
 * Get the error bits set by the device if the operation failed.
 *
 * @param otbn OTBN instance
 * @param[out] err_bits The error bits returned by the hardware.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_get_err_bits(const dif_otbn_t *otbn,
                                   dif_otbn_err_bits_t *err_bits);

/**
 * Gets the number of executed OTBN instructions.
 *
 * Gets the number of instructions executed so far in the current OTBN run if
 * there is one. Otherwise, gets the number executed in total in the previous
 * OTBN run.
 *
 * @param otbn OTBN instance
 * @param[out] insn_cnt The number of instructions executed by OTBN.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_get_insn_cnt(const dif_otbn_t *otbn, uint32_t *insn_cnt);

/**
 * Write an OTBN application into its instruction memory (IMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in IMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len_bytes number of bytes to copy.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_imem_write(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                 const void *src, size_t len_bytes);

/**
 * Read from OTBN's instruction memory (IMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in IMEM the first word is read from
 * @param[out] dest the main memory location to copy the data to (preallocated)
 * @param len_bytes number of bytes to copy.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_imem_read(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                void *dest, size_t len_bytes);

/**
 * Write to OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in DMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len_bytes number of bytes to copy.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_dmem_write(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                 const void *src, size_t len_bytes);

/**
 * Read from OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param otbn OTBN instance
 * @param offset_bytes the byte offset in DMEM the first word is read from
 * @param[out] dest the main memory location to copy the data to (preallocated)
 * @param len_bytes number of bytes to copy.
 * @return The result of the operation.
 */
dif_result_t dif_otbn_dmem_read(const dif_otbn_t *otbn, uint32_t offset_bytes,
                                void *dest, size_t len_bytes);

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
