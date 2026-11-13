/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Keymgr interface driver */

.globl keymgr_init
.globl keymgr_rcv
.globl keymgr_rsp

/*

This file contains the keymgr interface driver such that HKDF can be computed
in SW on OTBN. This driver is used to receive the binding values and finally
send the derived key back to the keymgr. It is controlled by CSRs and WSRs:

  - KEYMGR_STATUS: Monitor the state of the interface
  - KEYMGR_CTRL: Trigger commands
  - The data WSRs: KEYMGR_MSG_S0_L, KEYMGR_MSG_S1_L,
                   KEYMGR_MSG_S0_H, KEYMGR_MSG_S1_H

A common usage case is to receive the binding values, compute the HKDF, and
send the derived key back. This unfolds in the following chain of routines:

  1. `keymgr_init`: Checks that the interface is ready a starts a session. The
     interface now starts to receive the message beats.
  2. `keymgr_rcv`: Receives message data.
  3. `keymgr_rsp`: Sends a response back to the keymgr.

This driver reserves the GRP x27 for polling timeouts. This register must not
be modified by any routine that makes use of the keymgr interface.

Further it is assumed that the GRPs x20-x26 are free to be used as temporary
registers and w31 is all zero.

*/

.text

/* Timeout value (number of iterations in `_keymgr_msg_valid_poll` and
 * `_keymgr_send_poll`) when polling the keymgr interface. */
.equ KEYMGR_POLL_MAX_ITERS, 1024

/* KEYMGR_STATUS bit masks. */
.equ KEYMGR_STATUS_RECEIVING, 0x1
.equ KEYMGR_STATUS_SENDING, 0x2
.equ KEYMGR_STATUS_MSG_VALID, 0x4
.equ KEYMGR_STATUS_MSG_COMPLETE, 0x8
.equ KEYMGR_STATUS_BUSY, 0x3
.equ KEYMGR_STATUS_STRB_MASK, 0xff
.equ KEYMGR_STATUS_STRB_OFFSET, 16

/* KEYMGR_CTRL commands. */
.equ KEYMGR_CTRL_START, 0x1
.equ KEYMGR_CTRL_SEND, 0x2

/**
 * Start a keymgr session. Checks that the interface is ready and then commands
 * it to start receiving. Crashes if the interface is not ready.
 */
keymgr_init:
  /* Crash if a previous session is still receiving or sending. */
  csrrs x24, KEYMGR_STATUS, x0
  andi x24, x24, KEYMGR_STATUS_BUSY
  beq x24, x0, _keymgr_start
  unimp

_keymgr_start:
  /* Set the timeout maximum value. */
  li x27, KEYMGR_POLL_MAX_ITERS

  /* Set a valid integrity on the receiving WSR. This is required as simulation
   * environments does not initialize the WSRs with valid integrity.
   */
  bn.wsrw KEYMGR_MSG_S0_L, w31
  /* Start the session. */
  addi x24, x0, KEYMGR_CTRL_START
  csrrw x0, KEYMGR_CTRL, x24

  ret

/**
 * Polling routines for the `KEYMGR_STATUS` register.
 */

_keymgr_msg_valid_poll:
  /* Crash if timeout. */
  bne x27, x0, _keymgr_msg_valid_poll_time_remaining
  unimp

_keymgr_msg_valid_poll_time_remaining:
  addi x27, x27, -1
  csrrs x24, KEYMGR_STATUS, x0
  andi x24, x24, KEYMGR_STATUS_MSG_VALID
  beq x24, x0, _keymgr_msg_valid_poll
  addi x27, x0, KEYMGR_POLL_MAX_ITERS
  ret

_keymgr_send_poll:
  /* Crash if timeout. */
  bne x27, x0, _keymgr_send_poll_time_remaining
  unimp

_keymgr_send_poll_time_remaining:
  addi x27, x27, -1
  csrrs x24, KEYMGR_STATUS, x0
  andi x24, x24, KEYMGR_STATUS_SENDING
  bne x24, x0, _keymgr_send_poll
  addi x27, x0, KEYMGR_POLL_MAX_ITERS
  ret

/**
 * Receive one message beat.
 *
 * @param[out] w0:  The received 64-bit message data. The message is always LSB
 *                  aligned and the strobe defines the validity of the bytes.
 * @param[out] x20: Message complete flag, 2^32-1 if this is the last message
 *                  part, 0 otherwise.
 * @param[out] x21: The strobe of the received message data. The lowest 8 bits
 *                  define the validity of the corresponding byte in w0.
 */
keymgr_rcv:
  /* Clear the complete flag and set a full strobe. */
  addi x20, x0, 0
  addi x21, x0, -1

  /* Poll until a message beat is received. */
  jal x1, _keymgr_msg_valid_poll

  /* Check if the message is complete. */
  csrrs x24, KEYMGR_STATUS, x0
  andi x20, x24, KEYMGR_STATUS_MSG_COMPLETE
  beq x20, x0, _keymgr_rcv_read
  /* If msg is complete, set the complete flag and capture the strobe. */
  addi x20, x0, -1
  srli x21, x24, KEYMGR_STATUS_STRB_OFFSET
  andi x21, x21, KEYMGR_STATUS_STRB_MASK

_keymgr_rcv_read:
  /* Read the message. */
  bn.wsrr w0, KEYMGR_MSG_S0_L
  ret

/**
 * Send a response.
 *
 * Sends a response back to the keymgr. Crashes if the interface is not in the
 * right state to send a response.
 *
 * @param[in] w0: Bits 255:0   of share 0 of the response.
 * @param[in] w1: Bits 511:256 of share 0 of the response.
 * @param[in] w2: Bits 255:0   of share 1 of the response.
 * @param[in] w3: Bits 511:256 of share 1 of the response.
 */
keymgr_rsp:
  /* Crash if the interface is not ready to send. */
  csrrs x24, KEYMGR_STATUS, x0
  andi x24, x24, KEYMGR_STATUS_MSG_COMPLETE
  bne x24, x0, _keymgr_rsp_load
  unimp

_keymgr_rsp_load:
  /* Load the response into the WSRs. */
  bn.wsrw KEYMGR_MSG_S0_L, w0
  bn.wsrw KEYMGR_MSG_S0_H, w1

  bn.xor w31, w31, w31 /* dummy */

  bn.wsrw KEYMGR_MSG_S1_L, w2
  bn.wsrw KEYMGR_MSG_S1_H, w3

  /* Send the response. */
  addi x24, x0, KEYMGR_CTRL_SEND
  csrrw x0, KEYMGR_CTRL, x24
  jal x1, _keymgr_send_poll

  ret
