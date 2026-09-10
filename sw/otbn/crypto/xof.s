/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Extendable-output function (XOF / SHAKE) hardware interface driver. */

.globl xof_shake128_init
.globl xof_shake256_init
.globl xof_sha3_256_init
.globl xof_sha3_512_init
.globl xof_absorb
.globl xof_process
.globl xof_squeeze24
.globl xof_squeeze32
.globl xof_finish

/*

This file contains the KMAC driver for usage of the SHAKE128 and SHAKE256 XOFs
in post-quantum cryptography implementations (ML-DSA, ML-KEM). The KMAC
interface is exclusively instrumented through dedicated CSRs:

    - KMAC_CTRL: Configuration of the algorithm (either SHAKE128 or SHAKE256).
    - KMAC_CMD: Trigger commands (`START`, `SEND`, `PROCESS`, `DONE`, etc.).
    - KMAC_STATUS: Monitor the state of the KMAC interface.

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
    4. `xof_squeeze{24,32}`: Squeeze bytes of shared data into WSRs.
    5. `xof_finish`: Indicate the end of the operation and liberate the KMAC
       block.

The KMAC interface requires drivers to poll the `KMAC_STATUS` CSR to monitor
whether an issued command has ended successfully or resulted in an error.
Furthermore, since the XOF output is squeezed out of a rate buffer that needs
to be refreshed periodically drivers need to track how many bytes are left in
this buffer. Consequently, this driver reserves three GPRs x28-x30 to achieve
these housekeeping tasks:

    x28: Remaining number of 64-bit chunks in the KMAC-internal rate buffer.
    x29: Size (number of 64-bit chunks) of the rate buffer.
    x30: Timeout value for the polling routines.

These registers must not be modified by any routine that makes use the KMAC
interface.

*/

/* Timeout value (number of iterations in `_xof_ready_poll` and
   `_xof_rsp_valid_poll`) when polling the KMAC interface. */
.set KMAC_POLL_MAX_ITERS, 1024

/* Size of the KMAC-internal rate buffer (number of 64-bit chunks) from which
   the XOF output is squeezed. */
.set KMAC_SHAKE128_RATE, 21
.set KMAC_SHAKE256_RATE, 17
.set KMAC_SHA3_256_RATE, 4
.set KMAC_SHA3_512_RATE, 8

/*
 * Register configuration values to instrument the KMAC interface.
 */

/* KMAC_START */
.set KMAC_CTRL_START, 0x1
.set KMAC_CTRL_SEND, 0x2
.set KMAC_CTRL_PROCESS, 0x4
.set KMAC_CTRL_DONE, 0x8
.set KMAC_CTRL_CLOSE, 0x10

/* KMAC_STATUS */
.set KMAC_STATUS_READY_MASK, 0x1
.set KMAC_STATUS_RSP_VALID_MASK, 0x2
.set KMAC_STATUS_ERROR_MASK, 0x1c

.text

/**
 * Initialize the KMAC interface with the desired algorithm.
 */
xof_shake128_init:
  /*
   * Configure SHAKE128 with EN_XOF=1, STRENGTH=L128(3'b000) and
   * MODE=AppShake(2'b01). The upper fields hold the bitwise inverted values:
   * EN_XOF_INV=0, STRENGTH_INV=3'b111, MODE_INV=2'b10.
   */
  li x24, 0x2e0011
  addi x28, x0, KMAC_SHAKE128_RATE
  addi x29, x0, KMAC_SHAKE128_RATE
  jal x0, _xof_shake_init

xof_sha3_256_init:
  /*
   * Configure SHA3-256 with EN_XOF=0, STRENGTH=L256(3'b010) and
   * MODE=AppSha3(2'b00). The upper fields hold the bitwise inverted values:
   * EN_XOF_INV=1, STRENGTH_INV=3'b101, MODE_INV=2'b11.
   */
  li x24, 0x3b0004
  addi x28, x0, KMAC_SHA3_256_RATE
  addi x29, x0, KMAC_SHA3_256_RATE
  jal x0, _xof_shake_init

xof_sha3_512_init:
  /*
   * Configure SHA3-512 with EN_XOF=0, STRENGTH=L512(3'b100) and
   * MODE=AppSha3(2'b00). The upper fields hold the bitwise inverted values:
   * EN_XOF_INV=1, STRENGTH_INV=3'b011, MODE_INV=2'b11.
   */
  li x24, 0x370008
  addi x28, x0, KMAC_SHA3_512_RATE
  addi x29, x0, KMAC_SHA3_512_RATE
  jal x0, _xof_shake_init

xof_shake256_init:
  /*
   * Configure SHAKE256 with EN_XOF=1, STRENGTH=L256(3'b010) and
   * MODE=AppShake(2'b01). The upper fields hold the bitwise inverted values:
   * EN_XOF_INV=0, STRENGTH_INV=3'b101, MODE_INV=2'b10.
   */
  li x24, 0x2a0015
  addi x28, x0, KMAC_SHAKE256_RATE
  addi x29, x0, KMAC_SHAKE256_RATE
_xof_shake_init:
  /* Set the timeout maximum value. Then poll until the KMAC is ready to start
     a session. Must come before the configuration is written. */
  addi x30, x0, KMAC_POLL_MAX_ITERS
  jal x1, _xof_ready_poll
  /* Write the configuration */
  csrrw x0, KMAC_CFG, x24
  /* Send the `START` command. */
  addi x24, x0, KMAC_CTRL_START
  csrrs x0, KMAC_CTRL, x24

  ret

/**
 * Polling routines for the `KMAC_STATUS` register.
 */

_xof_ready_poll:
  /* Crash if timeout. */
  bne x30, x0, _xof_ready_poll_time_remaining
  unimp

_xof_ready_poll_time_remaining:
  addi x30, x30, -1
  csrrs x25, KMAC_STATUS, x0
  andi x25, x25, KMAC_STATUS_READY_MASK
  beq x25, x0, _xof_ready_poll
  addi x30, x0, KMAC_POLL_MAX_ITERS
  ret

_xof_rsp_valid_poll:
  /* Crash timeout. */
  bne x30, x0, _xof_rsp_valid_poll_time_remaining
  unimp

_xof_rsp_valid_poll_time_remaining:
  addi x30, x30, -1
  csrrs x25, KMAC_STATUS, x0
  andi x25, x25, KMAC_STATUS_RSP_VALID_MASK
  beq x25, x0, _xof_rsp_valid_poll
  addi x30, x0, KMAC_POLL_MAX_ITERS
  ret

/**
 * Finish the KMAC session and release the block. Must be called after each
 * session and xof_process must be called before it.
 */
xof_finish:
  /* Poll until the interface is ready to accept a command. */
  jal x1, _xof_ready_poll

  /* Send the `DONE` command. */
  addi x24, x0, KMAC_CTRL_DONE
  csrrs x0, KMAC_CTRL, x24

  /* Wait for the finish response acknowledging the end of the session. */
  jal x1, _xof_rsp_valid_poll

  /* Check for errors in the finish response but defer acting on it until the
     session is closed. */
  csrrs x24, KMAC_STATUS, x0
  andi x24, x24, KMAC_STATUS_ERROR_MASK

  /* Always close the session even on an error. */
  addi x25, x0, KMAC_CTRL_CLOSE
  csrrs x0, KMAC_CTRL, x25

  /* Crash in case of an error. */
  beq x24, x0, _xof_finish_success
  unimp

_xof_finish_success:
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

  /* Poll until the interface is ready to accept a message. */
  jal x1, _xof_ready_poll

  /* x = n - 32. */
  addi  x24, x20, -32

  /* n = 0, if x < 32, else n = n - 32. */
  srai x25, x24, 31
  and x25, x24, x25
  sub x20, x24, x25

  /* x = 2^32-1 >> (32 - x). */
  sub   x24, x0, x25
  addi  x25, x0, -1
  srl   x24, x25, x24

  /*
   * Set the strobe register value such that
   *
   *    KMAC_BYTE_STROBE = 2^32-1 >> (32 - x),
   *
   * where x = 32, if n >= 32, else x = n.
   */
  csrrw x0, KMAC_STRB, x24

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

  addi x24, x0, 27
  bn.lid x24, 0(x22++)
  bn.wsrw KMAC_DATA_S1, w27

_xof_absorb_masked_end:

  /* Trigger the absorption of the written message word. */
  addi x24, x0, KMAC_CTRL_SEND
  csrrw x0, KMAC_CTRL, x24

  /* Absorb the next chunk of <= 32 message bytes. */
  jal  x0, xof_absorb

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
  /* Poll before sending the `PROCESS` command. */
  jal x1, _xof_ready_poll

  /* Send the `PROCESS` command. */
  addi x24, x0, KMAC_CTRL_PROCESS
  csrrs x0, KMAC_CTRL, x24

  /* Poll until the `PROCESS` command has been accepted and the first digest
     response arrives. */
  jal x1, _xof_rsp_valid_poll

  /* Check the first response for errors but do not read it yet. */
  csrrs x24, KMAC_STATUS, x0
  andi x24, x24, KMAC_STATUS_ERROR_MASK

  /* Finish in case of an error. */
  bne x24, x0, xof_finish

  ret

/**
 * Squeeze out 32 Boolean-shared bytes into w29 and w30.
 *
 * Depending on how many bytes are remaining in the KMAC-internal rate buffer,
 * this routine might trigger a `RUN` command that starts a new KMAC round
 * computation repopulating the rate buffer. This routine *must* only be
 * called after having issued the `PROCESS` command (see `xof_process`).
 */
xof_squeeze32:
  /* Squeeze the 32 bytes in chunks of 64 bits from the KMAC-internal rate
     buffer. */
  loopi 4, 8

    /* Only issue the `RUN` command if there are fewer than 64 bits remaining in
       the rate buffer. */
    bne x28, x0, _xof_squeeze32_recharge

    /* Poll before reading the data registers. */
    jal x1, _xof_rsp_valid_poll

    /* Reset the rate counter. */
    addi x28, x29, 0

_xof_squeeze32_recharge:

    /* Transfer the 32 squeezed and Boolean shared bytes to w29 and w30. */
    bn.wsrr w27, KMAC_DATA_S0
    bn.rshi w29, w27, w29 >> 64

    addi x28, x28, -1

    bn.wsrr w28, KMAC_DATA_S1
    bn.rshi w30, w28, w30 >> 64
    /* End of loop */

  ret

/**
 * Squeeze out 24 Boolean-shared bytes into w29 and w30 (see `xof_squeeze32`).
 *
 * CAUTION: Only use this routine with SHAKE128. Since the rate of SHAKE128 is
 * 21 64-bit blocks we only need to poll when only need to poll when the rate
 * is exhausted. The rate buffer is guaranteed to hold a multiple of 3 64-bit
 * blocks.
 */
xof_squeeze24:
  /* Skip the polling if the rate buffer is not empty. */
  bne x28, x0, _xof_squeeze24_recharge

  jal x1, _xof_rsp_valid_poll

  addi x28, x29, 0

_xof_squeeze24_recharge:

  /* Squeeze the 24 bytes in chunks of 64 bits from the KMAC-internal rate
     buffer. */

  loopi 3, 5
    /* Transfer the 24 squeezed and Boolean shared bytes to w29 and w30. */
    bn.wsrr w27, KMAC_DATA_S0
    bn.rshi w29, w27, w29 >> 64

    addi x28, x28, -1

    bn.wsrr w28, KMAC_DATA_S1
    bn.rshi w30, w28, w30 >> 64
    /* End of loop */

  bn.rshi w29, w27, w29 >> 64
  bn.xor w31, w31, w31 /* dummy */
  bn.rshi w30, w28, w30 >> 64

  ret
