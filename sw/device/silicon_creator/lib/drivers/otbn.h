// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTBN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTBN_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The size of OTBN's data memory in bytes.
 */
extern const size_t kOtbnDMemSizeBytes;

/**
 * The size of OTBN's instruction memory in bytes.
 */
extern const size_t kOtbnIMemSizeBytes;

/**
 * OTBN commands
 */
typedef enum otbn_cmd {
  kOtbnCmdExecute = 0xd8,
  kOtbnCmdSecWipeDmem = 0xc3,
  kOtbnCmdSecWipeImem = 0x1e,
} otbn_cmd_t;

/**
 * OTBN status
 */
typedef enum otbn_status {
  kOtbnStatusIdle = 0x00,
  kOtbnStatusBusyExecute = 0x01,
  kOtbnStatusBusySecWipeDmem = 0x02,
  kOtbnStatusBusySecWipeImem = 0x03,
  kOtbnStatusBusySecWipeInt = 0x04,
  kOtbnStatusLocked = 0xFF,
} otbn_status_t;

/**
 * The following constants represent the expected number of sec_mmio register
 * writes performed by functions in provided in this module. See
 * `SEC_MMIO_WRITE_INCREMENT()` for more details.
 *
 * Example:
 * ```
 *  otbn_execute();
 *  SEC_MMIO_WRITE_INCREMENT(kOtbnSecMMioExecute);
 * ```
 */
enum {
  kOtbnSecMmioExecute = 1,
  kOtbnSecMmioSetCtrlSwErrsFatal = 1,
};

/**
 * Start the execution of the application loaded into OTBN.
 *
 * This function blocks until OTBN is idle.
 *
 * @return Result of the operation.
 */
rom_error_t otbn_execute(void);

/**
 * Is OTBN busy executing an application?
 *
 * @return OTBN is busy
 */
bool otbn_is_busy(void);

/**
 * OTBN Internal Errors
 *
 * OTBN uses a bitfield to indicate which errors have been seen. Multiple errors
 * can be seen at the same time. This enum gives the individual bits that may be
 * set for different errors.
 */
typedef enum otbn_err_bits {
  kOtbnErrBitsNoError = 0,
  /** A BAD_DATA_ADDR error was observed. */
  kOtbnErrBitsBadDataAddr = (1 << 0),
  /** A BAD_INSN_ADDR error was observed. */
  kOtbnErrBitsBadInsnAddr = (1 << 1),
  /** A CALL_STACK error was observed. */
  kOtbnErrBitsCallStack = (1 << 2),
  /** An ILLEGAL_INSN error was observed. */
  kOtbnErrBitsIllegalInsn = (1 << 3),
  /** A LOOP error was observed. */
  kOtbnErrBitsLoop = (1 << 4),
  /** A IMEM_INTG_VIOLATION error was observed. */
  kOtbnErrBitsImemIntgViolation = (1 << 16),
  /** A DMEM_INTG_VIOLATION error was observed. */
  kOtbnErrBitsDmemIntgViolation = (1 << 17),
  /** A REG_INTG_VIOLATION error was observed. */
  kOtbnErrBitsRegIntgViolation = (1 << 18),
  /** A BUS_INTG_VIOLATION error was observed. */
  kOtbnErrBitsBusIntgViolation = (1 << 19),
  /** A BAD_INTERNAL_STATE error was observed. */
  kDifOtbnErrBitsBadInternalState = (1 << 20),
  /** An ILLEGAL_BUS_ACCESS error was observed. */
  kOtbnErrBitsIllegalBusAccess = (1 << 21),
  /** A LIFECYCLE_ESCALATION error was observed. */
  kOtbnErrBitsLifecycleEscalation = (1 << 22),
  /** A FATAL_SOFTWARE error was observed. */
  kOtbnErrBitsFatalSoftware = (1 << 23),
  kOtbnErrBitsLast = kOtbnErrBitsFatalSoftware,
} otbn_err_bits_t;

/**
 * Get the error bits set by the device if the operation failed.
 *
 * @param[out] err_bits The error bits returned by the hardware.
 */
void otbn_err_bits_get(otbn_err_bits_t *err_bits);

/**
 * Read OTBN's instruction count register.
 *
 * OTBN automatically calculates how many instructions are executed in a given
 * program and writes the result to this register. Software can read it to
 * verify that instructions were not unexpectedly skipped or added (for
 * instance, due to fault injection attacks).
 *
 * Note that the OTBN hardware resets the instruction count register to 0 when
 * the EXECUTE command is issued, so there is no need for software to reset the
 * counter between programs.
 *
 * @return count the value from the instruction count register
 */
uint32_t otbn_instruction_count_get(void);

/**
 * Wipe IMEM securely.
 *
 * This function blocks until OTBN is idle.
 *
 * @return Result of the operation.
 */
rom_error_t otbn_imem_sec_wipe(void);

/**
 * Write an OTBN application into its instruction memory (IMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param offset_bytes the byte offset in IMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len number of words to copy.
 * @return `kErrorOtbnBadOffset` if `offset_bytes` isn't word aligned,
 * `kErrorOtbnBadOffsetLen` if `len` is invalid , `kErrorOk` otherwise.
 */
rom_error_t otbn_imem_write(uint32_t offset_bytes, const uint32_t *src,
                            size_t len);

/**
 * Wipe DMEM securely.
 *
 * This function blocks until OTBN is idle.
 *
 * @return Result of the operation.
 */
rom_error_t otbn_dmem_sec_wipe(void);

/**
 * Write to OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param offset_bytes the byte offset in DMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len number of words to copy.
 * @return `kErrorOtbnBadOffset` if `offset_bytes` isn't word aligned,
 * `kErrorOtbnBadOffsetLen` if `len` is invalid , `kErrorOk` otherwise.
 */
rom_error_t otbn_dmem_write(uint32_t offset_bytes, const uint32_t *src,
                            size_t len);

/**
 * Read from OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param offset_bytes the byte offset in DMEM the first word is read from
 * @param[out] dest the main memory location to copy the data to (preallocated)
 * @param len number of words to copy.
 * @return `kErrorOtbnBadOffset` if `offset_bytes` isn't word aligned,
 * `kErrorOtbnBadOffsetLen` if `len` is invalid , `kErrorOk` otherwise.
 */
rom_error_t otbn_dmem_read(uint32_t offset_bytes, uint32_t *dest, size_t len);

/**
 * Zero out the contents of OTBN's data memory (DMEM).
 */
void otbn_zero_dmem(void);

/**
 * Sets the software errors are fatal bit in the control register.
 *
 * When set any software error becomes a fatal error. The bit can only be
 * changed when the OTBN status is IDLE.
 *
 * @param enable Enable or disable whether software errors are fatal.
 */
void otbn_set_ctrl_software_errs_fatal(bool enable);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_OTBN_H_
