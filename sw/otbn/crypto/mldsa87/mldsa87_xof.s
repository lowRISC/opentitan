/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Extendable-output function interface. */

.globl xof_shake128_init
.globl xof_shake256_init
.globl xof_absorb
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

/**
 * Absorb a message of size n bytes.
 *
 * Supports the absorption of both masked (two equally-sized Boolean shares at
 * DMEM[x21], DMEM[x22]) and unmasked (message at DMEM[x21] and x22 = 0) input
 * messages. This routine *must* only be called after the initialization of the
 * KMAC interface (see `xof_{shake128,shake256}_init`)
 *
 * @param[in] x20: n, size of the input message.
 * @param[in] x21: DMEM address of the 1st message share.
 * @param[in] x22: DMEM address of the 2nd message share (0 if unmasked)
 */
xof_absorb:
  /* Exit the absorption loop, if n == 0.  */
  beq x20, x0, _xof_absorb_end

  /*
   * Set the strobe register value such that
   *
   *    KMAC_BYTE_STROBE = 2^32-1 >> (32 - x),
   *
   * where x = 32, if n >= 32, else x = n.
   */
  addi x25, x0, 32

  /* x = 2^32-1, if n < 32, else x = 0. */
  sub x24, x20, x25
  srai x26, x24, 31

  /* x = n, if x == 2^32-1, else x = 32. */
  and x24, x24, x26
  add x24, x25, x24

  /* (32 - x). */
  sub x25, x25, x24

  /* 2^32-1 >> (32 - x). */
  addi x24, x0, -1
  srl x24, x24, x25

  csrrw x0, KMAC_BYTE_STROBE, x24

  /* Make sure KMAC is ready to absorb data. */
  addi x24, x0, KMAC_IF_STATUS_MSG_WRITE_RDY
  jal x1, _xof_kmac_if_status_poll

  bne x22, x0, _xof_absorb_masked_begin

  /* Pass the unshared message to the KMAC interface. */
  addi x24, x0, 26
  bn.lid x24, 0(x21++)
  bn.wsrw KMAC_DATA_S0, w26
  bn.wsrw KMAC_DATA_S1, w31
  jal x0, _xof_absorb_masked_end

_xof_absorb_masked_begin:

  /* Pass the message word to the KMAC interface, ensuring that the shares are
     not combined in an unsecure fashion. */
  addi x24, x0, 26
  bn.lid x24, 0(x21++)
  bn.wsrw KMAC_DATA_S0, w26

  bn.xor w31, w31, w31 /* dummy */

  addi x24, x0, 27
  bn.lid x24, 0(x22++)
  bn.wsrw KMAC_DATA_S1, w27

_xof_absorb_masked_end:

  /* Trigger the absorption of the written message word. */
  addi x24, x0, 1
  csrrw x0, KMAC_MSG_SEND, x24

  /*
   * Decrement the number of remaining message bytes such that
   *
   *    n = max(n - 32, 0).
   */

  /* (n - 32) */
  addi x20, x20, -32

  /* n = max(n - 32, 0). */
  srai x24, x20, 31
  addi x25, x0, -1
  xor x24, x24, x25
  and x20, x20, x24

  /* Absorb the next chunk of <= 32 message bytes. */
  jal x0, xof_absorb

_xof_absorb_end:
  ret

/**
 * Send the `PROCESS` command to the KMAC interface to process the absorbed
 * message and transfer the module into the `SQUEEZE` state.
 *
 * This routine *must* only be called after the initialization of the KMAC
 * interface (see `xof_{shake128,shake256}_init`) and *must* be called even if
 * there was no message absorption in order to be able to squeeze the digest.
 */
xof_process:
  /* Trigger the processing of the absorbed message. */
  addi x24, x0, KMAC_CMD_PROCESS
  csrrw x0, KMAC_CMD, x24

  /* Poll until the first 64-bit digest is ready to be read out. */
  addi x24, x0, KMAC_IF_STATUS_DIGEST_VALID
  jal x1, _xof_kmac_if_status_poll

  ret
