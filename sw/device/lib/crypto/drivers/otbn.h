// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_OTBN_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_OTBN_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

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
 * Error codes for the OTBN driver.
 */
typedef enum otbn_error {
  /** No errors. */
  kOtbnErrorOk = 0,
  /** Invalid argument provided to OTBN interface function. */
  kOtbnErrorInvalidArgument = 1,
  /** Invalid offset provided. */
  kOtbnErrorBadOffsetLen = 2,
  /** OTBN internal error; use otbn_get_err_bits for specific error codes. */
  kOtbnErrorExecutionFailed = 3,
  /** Attempt to interact with OTBN while it was unavailable. */
  kOtbnErrorUnavailable = 4,
} otbn_error_t;

/**
 * Evaluate an expression and return if the result is an error.
 *
 * @param expr_ An expression which results in an otbn_error_t.
 */
#define OTBN_RETURN_IF_ERROR(expr_)     \
  do {                                  \
    otbn_error_t local_error_ = expr_;  \
    if (local_error_ != kOtbnErrorOk) { \
      return local_error_;              \
    }                                   \
  } while (0)

/**
 * Start the execution of the application loaded into OTBN.
 */
void otbn_execute(void);

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
} otbn_err_bits_t;

/**
 * Get the error bits set by the device if the operation failed.
 *
 * @param[out] err_bits The error bits returned by the hardware.
 */
void otbn_get_err_bits(otbn_err_bits_t *err_bits);

/**
 * Write an OTBN application into its instruction memory (IMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param offset_bytes the byte offset in IMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len number of words to copy.
 * @return `kOtbnErrorBadOffset` if `offset_bytes` isn't word aligned,
 * `kOtbnErrorBadOffsetLen` if `len` is invalid , `kOtbnErrorOk` otherwise.
 */
otbn_error_t otbn_imem_write(uint32_t offset_bytes, const uint32_t *src,
                             size_t len);

/**
 * Write to OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param offset_bytes the byte offset in DMEM the first word is written to
 * @param src the main memory location to start reading from.
 * @param len number of words to copy.
 * @return `kOtbnErrorBadOffset` if `offset_bytes` isn't word aligned,
 * `kOtbnErrorBadOffsetLen` if `len` is invalid , `kOtbnErrorOk` otherwise.
 */
otbn_error_t otbn_dmem_write(uint32_t offset_bytes, const uint32_t *src,
                             size_t len);

/**
 * Read from OTBN's data memory (DMEM)
 *
 * Only 32b-aligned 32b word accesses are allowed.
 *
 * @param offset_bytes the byte offset in DMEM the first word is read from
 * @param[out] dest the main memory location to copy the data to (preallocated)
 * @param len number of words to copy.
 * @return `kOtbnErrorBadOffset` if `offset_bytes` isn't word aligned,
 * `kOtbnErrorBadOffsetLen` if `len` is invalid , `kOtbnErrorOk` otherwise.
 */
otbn_error_t otbn_dmem_read(uint32_t offset_bytes, uint32_t *dest, size_t len);

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
 * @return `kOtbnErrorUnavailable` if the requested change cannot be made or
 * `kOtbnErrorOk` otherwise.
 */
otbn_error_t otbn_set_ctrl_software_errs_fatal(bool enable);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_OTBN_H_
