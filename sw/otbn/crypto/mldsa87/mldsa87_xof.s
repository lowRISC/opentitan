/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Extendable-output function interface. */

.globl xof_shake128_init
.globl xof_shake256_init
.globl xof_finish

/*
 * XXX: Driver is not final and may change. Awaiting KMAC interface circuit.
 */

/*

This file contains the KMAC driver for usage of the SHAKE128 and SHAKE256 XOFs
in the ML-DSA implementation. The KMAC interface is exclusively instrumented
through dedicated CSRs:

    - KMAC_CFG: Configuration of the algorithm (either SHAKE128 or SHAKE256).
    - KMAC_CMD: Trigger comp. stages (`START`, `PROCESS`, `RUN`, `FINISH`).
    - KMAC_STATUS: Monitor the state of the KMAC interface.
    - KMAC_IF_STATUS: Monitor readiness to read/write data to the interface.
    - KMAC_INTR: Monitor the interrupt vector of the KMAC interface.

A common usage case is the absorption and squeezing of data that unfolds with
following chain of routines:

    1. `xof_shake{128,256}_init`: Initialize the KMAC interface by specifying
       the desired algorithm. If successful, the KMAC hardware block is now
       attached to this process and cannot be interrupted with requests from
       other processes.
    2. `xof_absorb`: Pass an n-byte shared (Boolean shares) or unshared message
       to the KMAC interface for absorption.
    3. `xof_process`: Indicate that the entire message has been absorbed and
       its processing should begin.
    4. `xof_squeeze32`: Squeeze 32 bytes of shared data into WSRs.
    5. `xof_finish`: Indicate the end of the operation and liberate the KMAC
       block.

The KMAC interface requires drivers to poll the `KMAC_STATUS` and
`KMAC_IF_STATUS` CSRs to monitor whether an issued command has ended
successfully or resulted in an error. Furthermore, since the XOF output is
squeezed out of a rate buffer that needs to be refreshed periodically (see
`KMAC_CMD_RUN`) drivers need to track how many bytes are left in this buffer.
Consequently, this driver reserves three GPRs x28-x30 to achieve these
housekeeping tasks:

    x28: Remaining number of 64-bit chunks in the KMAC-internal rate buffer.
    x29: Size (number of 64-bit chunks) of the rate buffer.
    x30: Timeout value for the polling routines.

These registers must not be modified by any routine that makes use the KMAC
interface.

*/

/* Timeout value (number of iterations in `_xof_kmac_status_poll` and
   `_xof_kmac_if_status_poll`) when polling the KMAC interface. */
.set KMAC_POLL_MAX_ITERS, 1024

/* Size of the KMAC-internal rate buffer (number of 64-bit chunks) from which
   the XOF output is squeezed. */
.set KMAC_SHAKE128_RATE, 21
.set KMAC_SHAKE256_RATE, 17

/*
 * Register configuration values to instrument the KMAC interface.
 */

/* KMAC_CFG */
.set KMAC_CFG_SHAKE128, 0x20
.set KMAC_CFG_SHAKE256, 0x24

/* KMAC_START */
.set KMAC_CMD_START, 0x1d
.set KMAC_CMD_PROCESS, 0x2e
.set KMAC_CMD_RUN, 0x31
.set KMAC_CMD_FINISH, 0x16

/* KMAC_STATUS */
.set KMAC_STATUS_BUSY, 0x0
.set KMAC_STATUS_IDLE, 0x1
.set KMAC_STATUS_ABSORB, 0x2
.set KMAC_STATUS_SQUEEZE, 0x4

/* KMAC_IF_STATUS */
.set KMAC_IF_STATUS_MSG_WRITE_RDY, 0x1
.set KMAC_IF_STATUS_DIGEST_VALID, 0x8

/* KMAC_INTR */
.set KMAC_INTR_ERROR, 0x1

.text

/**
 * Initialize the KMAC interface with the desired algorithm.
 *
 * If any error is encountered, this routine will trap the OTBN process by
 * issuing an `unimp` instruction.
 */
xof_shake128_init:
  addi x24, x0, KMAC_CFG_SHAKE128
  csrrw x0, KMAC_CFG, x24
  addi x28, x0, KMAC_SHAKE128_RATE
  addi x29, x0, KMAC_SHAKE128_RATE
  jal x0, _xof_shake_init
xof_shake256_init:
  addi x24, x0, KMAC_CFG_SHAKE256
  csrrw x0, KMAC_CFG, x24
  addi x28, x0, KMAC_SHAKE256_RATE
  addi x29, x0, KMAC_SHAKE256_RATE
_xof_shake_init:
  /* Clear error bit in the KMAC_INTR register. */
  addi x24, x0, KMAC_INTR_ERROR
  csrrw x0, KMAC_INTR, x24

  /* Set the timeout maximum value. */
  addi x30, x0, KMAC_POLL_MAX_ITERS

  /* Make sure the KMAC block is idle. Note that until we issue a successful
     `START` command the KMAC block can still be claimed by other actors. */
  addi x24, x0, KMAC_STATUS_IDLE
  jal x1, _xof_kmac_status_poll

  /* Trigger a new XOF computation. */
  addi x24, x0, KMAC_CMD_START
  csrrw x0, KMAC_CMD, x24

  /* Transfer the KMAC block to the absorption stage. */
  addi x24, x0, KMAC_STATUS_ABSORB
  jal x1, _xof_kmac_status_poll

  /* Any error during the initialization will abort the OTBN process. */
  csrrs x24, KMAC_INTR, x0
  bne x24, x0, _xof_fail

  ret

/**
 * Polling routines for the `KMAC_STATUS` and `KMAC_STATUS_IF` CSRs.
 *
 * @param[in] x24: Expected value in the CSR.
 */
_xof_kmac_status_poll:
  beq x30, x0, _xof_fail
  addi x30, x30, -1
  csrrs x25, KMAC_STATUS, x0
  bne x24, x25, _xof_kmac_status_poll
  addi x30, x0, KMAC_POLL_MAX_ITERS
  ret
_xof_kmac_if_status_poll:
  beq x30, x0, _xof_fail
  addi x30, x30, -1
  csrrs x25, KMAC_IF_STATUS, x0
  bne x24, x25, _xof_kmac_if_status_poll
  addi x30, x0, KMAC_POLL_MAX_ITERS
  ret

/* Errors are not recoverable and result in an aborted process. */
_xof_fail:
  /* Still attempt to liberate the KMAC block before crashing. */
  addi x24, x0, KMAC_CMD_FINISH
  csrrw x0, KMAC_CMD, x24
  unimp

/**
 * Send the `FINISH` command to the KMAC interface to indicate liberate the
 * module. Every XOF session *must* be terminated with this routine before
 * starting a new one.
 */
xof_finish:
  addi x24, x0, KMAC_CMD_FINISH
  csrrw x0, KMAC_CMD, x24
  ret
