/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * A simple program showcasing how to use the KMAC interface.
 *
 * This test is intended to be run as a Top-Level-Test. The KMAC module must be setup correctly by
 * the system software before OTBN is started.
 *
 */
.global main

.text

main:
  jal x1, _shake_128
  jal x1, _shake_256
  jal x1, _sha3_256
  ecall

/**
 * SHAKE-128 test
 */
_shake_128:
  /* Configure SHAKE-128 with EN_XOF=1, STRENGTH=L128(3'b000), and MODE=AppShake(2'b01).
   * The upper fields hold the bitwise inverted values: EN_XOF_INV=0, STRENGTH_INV=3'b111,
   * MODE_INV=2'b10. */
  li x10, 0x2e0011
  csrrw x0, KMAC_CFG, x10

  jal x1, _hash_message

  /* Read 24 digest beats (beats 1-21 from the first rate, 22-24 from the second squeeze). */
  li x20, 24 /* Must be multiple of 4 */
  la x3, digest_shake_128
  jal x1, _read_digest

  /* Terminate the session. */
  jal x1, _terminate_session

  ret

/**
 * SHAKE-256 test
 */
_shake_256:
  /* Configure SHAKE-256 with EN_XOF=1, STRENGTH=L256(3'b010), and MODE=AppShake(2'b01).
   * The upper fields hold the bitwise inverted values: EN_XOF_INV=0, STRENGTH_INV=3'b101,
   * MODE_INV=2'b10. */
  li x10, 0x2a0015
  csrrw x0, KMAC_CFG, x10

  jal x1, _hash_message

  /* Read 24 digest beats (beat 1-17 from the first rate, 18-24 from the second squeeze). */
  li x20, 24 /* Must be multiple of 4 */
  la x3, digest_shake_256
  jal x1, _read_digest

  /* Terminate the session. */
  jal x1, _terminate_session

  ret

/**
 * SHA3-256 test
 */
_sha3_256:
  /* Configure SHA3-256 with EN_XOF=0, STRENGTH=L256(3'b010), and MODE=AppSha3(2'b00).
   * The upper fields hold the bitwise inverted values: EN_XOF_INV=1, STRENGTH_INV=3'b101,
   * MODE_INV=2'b11. */
  li x10, 0x3b0004
  csrrw x0, KMAC_CFG, x10

  jal x1, _hash_message

  /* Read 256 bits of digest (4 beats). */
  li x20, 4 /* Must be multiple of 4 */
  la x3, digest_sha3_256
  jal x1, _read_digest

  /* Terminate the session. */
  jal x1, _terminate_session

  ret

/**
 * Start a session, send the message, start the processing, and wait for the response.
 * Checks the response for errors.
 */
_hash_message:
  jal x1, _start_and_send_msg
  jal x1, _process

  /* Wait for the first response and then check the error */
  jal x1, _poll_rsp_valid
  jal x1, _check_rsp_error

  ret

/**
 * Start a session and send a fixed message.
 *
 * The message is expected to be 36 bytes long.
 * Clobbers: x2, x3, x10, w0, w1
 */
_start_and_send_msg:
  /* Poll until ready */
  jal x1, _poll_ready

  /* Start the session by issuing the START command. */
  li x10, 0x1
  csrrs x0, KMAC_CTRL, x10

  /* Poll until ready to accept the message. */
  jal x1, _poll_ready

  /* Load the first part of the message into w0. */
  li x2, 0
  la x3, msg
  bn.lid x2, 0(x3)

  /* Write 1st part of message unmasked (share 1 = 0) into the data WSRs. */
  bn.wsrw KMAC_DATA_S0, w0
  bn.xor w1, w1, w1
  bn.wsrw KMAC_DATA_S1, w1

  /* Set byte strobe: all 32 bytes of the 256-bit message are valid. */
  li x10, -1
  csrrw x0, KMAC_STRB, x10

  /* Issue SEND command. */
  li x10, 0x2
  csrrs x0, KMAC_CTRL, x10

  /* Poll until first message part is sent. */
  jal x1, _poll_ready

  /* Load the second part of the message into w0. */
  li x2, 0
  la x3, msg2
  bn.lid x2, 0(x3)

  /* Write 2nd part of message unmasked (share 1 = 0) into the data WSRs. */
  bn.wsrw KMAC_DATA_S0, w0
  bn.xor w1, w1, w1
  bn.wsrw KMAC_DATA_S1, w1

  /* Set byte strobe: only the first 4 bytes of the second message part are valid. */
  li x10, 0xf
  csrrw x0, KMAC_STRB, x10

  /* Issue 2nd SEND command. */
  li x10, 0x2
  csrrs x0, KMAC_CTRL, x10

  ret

/**
 * Issues the PROCESS command as soon as the interface is ready.
 * Clobbers: x2, x10
 */
_process:
  jal x1, _poll_ready
  li x10, 0x4
  csrrs x0, KMAC_CTRL, x10
  ret

/**
 * Reads digest data and stores it to DMEM.
 *
 * @param[in] x20: Number of 64-bit digest words to read. Must be a multiple of 4.
 * @param[out] x3: Pointer to the location in DMEM where the digest is placed.
 * Clobbers: x2, w0, w1, w2, x30
 */
_read_digest:
  li x30, 2
  bn.xor w2, w2, w2
_read_loop:
  /* We are lazy when merging beats, so unroll the loop 4x. */

  /* Read one beat */
  /* Merge 64-bit digest data into temporary register */

  jal x1, _read_beat /* into w0 */
  bn.rshi w2, w0, w2 >> 64

  jal x1, _read_beat
  bn.rshi w2, w0, w2 >> 64

  jal x1, _read_beat
  bn.rshi w2, w0, w2 >> 64

  jal x1, _read_beat
  bn.rshi w2, w0, w2 >> 64

  /* Write the merged beat to memory. */
  bn.sid x30, 0(x3++)

  addi x20, x20, -4
  bne x20, x0, _read_loop

  ret

/**
 * Reads one beat of the digest and unmask it into w0.
 *
 * Stalls until a digest beat is available. Checks the digest response for errors and terminates
 * the session if an error is detected. The termination results in a crash.
 *
 * @param[out] w0: Unmasked digest beat read from the data WSRs.
 * Clobbers: x2, w1
 */
_read_beat:
  /* Poll RSP_VALID before reading each beat. */
  jal x1, _poll_rsp_valid

  /* Read both shares. */
  bn.wsrr w0, KMAC_DATA_S0
  bn.wsrr w1, KMAC_DATA_S1

  /* Unmask the digest. */
  bn.xor w0, w0, w1
  ret

/**
 * Polls KMAC_STATUS.READY until it is set.
 * Clobbers: x2
 */
_poll_ready:
  csrrs x2, KMAC_STATUS, x0
  andi x2, x2, 0x1
  beq x2, x0, _poll_ready
  ret

/**
 * Polls KMAC_STATUS.RSP_VALID until it is set.
 * Clobbers: x2
 */
_poll_rsp_valid:
  csrrs x2, KMAC_STATUS, x0
  andi x2, x2, 0x2
  beq x2, x0, _poll_rsp_valid
  ret

_check_rsp_error:
  /* If there is an error, end the session immediately. */
  csrrs x2, KMAC_STATUS, x0
  andi x2, x2, 0x1c
  beq x2, x0, _check_rsp_error_success
  jal x1, _terminate_session
  unimp /* If there was an error, the session termination should crash. */
_check_rsp_error_success:
  ret

/**
  * Terminates a session.
  *
  * Issues the DONE command, polls for the finish response and checks it for errors. Once the
  * finish response was handled, issues the CLOSE command to end the session and release the
  * interface. Crashes if an error is detected.
  *
  * Clobbers: x2, x10
  */
_terminate_session:
  li x10, 0x8
  csrrs x0, KMAC_CTRL, x10

  /* Wait for the finish response acknowledging the end of the session. */
  jal x1, _poll_rsp_valid

  /* Check for errors in the finish response but defer acting on it until the session is closed. */
  csrrs x2, KMAC_STATUS, x0
  andi x2, x2, 0x4

  /* Always close the session even on an error. */
  li x10, 0x10
  csrrs x0, KMAC_CTRL, x10

  /* Crash if the finish response signaled an error, now that the session is closed. */
  beq x2, x0, _terminate_session_successful
  unimp

_terminate_session_successful:
  ret

.section .data

/* Test vector: bytes 0x00 through 0x23, written as little-endian 32-bit words.
 * Message: 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20212223
 */
msg:
  .word 0x03020100
  .word 0x07060504
  .word 0x0b0a0908
  .word 0x0f0e0d0c
  .word 0x13121110
  .word 0x17161514
  .word 0x1b1a1918
  .word 0x1f1e1d1c
msg2:
  /* 2nd part - only 4 bytes are valid */
  .word 0x23222120
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

.globl digest_shake_128
digest_shake_128:
  .zero 192 /* 24 beats, 8 bytes each */
/* Expected digest (big endian):
 * Beat 00: 0x 0c3703b56e0e78a8
 * Beat 01: 0x 1f96cdeaa2a63cbf
 * Beat 02: 0x f7a72c108813e74f
 * Beat 03: 0x 9b42ebebba78e9dd
 * Beat 04: 0x bc133c7bac8676a2
 * Beat 05: 0x 34a1587c79dad6d2
 * Beat 06: 0x 4bd883b7c8dc7ece
 * Beat 07: 0x 43169d5412b1d4ae
 * Beat 08: 0x 47a28923ef35e1eb
 * Beat 09: 0x d43c50703b5b24a3
 * Beat 10: 0x b81575d59260ad21
 * Beat 11: 0x e5102637e3d1d6ab
 * Beat 12: 0x 0c77cf48f12ab7ab
 * Beat 13: 0x 2693af95de37785e
 * Beat 14: 0x 1536a3f0fcdef144
 * Beat 15: 0x 89da427ea58b10b7
 * Beat 16: 0x 9fee4a31a694a08d
 * Beat 17: 0x d2038d8a6786203a
 * Beat 18: 0x e55f8d67b1cd5cbd
 * Beat 19: 0x cac54d08d88ec0a4
 * Beat 20: 0x 0d812269fd1ddad9
 * Beat 21: 0x ce00146dc96324e1
 * Beat 22: 0x 0f6f74e0134b27d1
 * Beat 23: 0x e1518eb527418212
 */

.globl digest_shake_256
digest_shake_256:
  .zero 192 /* 24 beats, 8 bytes each */
/* Expected digest (big endian):
 * Beat 00: 0x 1e1c33cf1b2f10e5
 * Beat 01: 0x 3d5fba6d5d675329
 * Beat 02: 0x c8bd9e17b6b958f6
 * Beat 03: 0x 86faede555c284c6
 * Beat 04: 0x 1385af839f503c29
 * Beat 05: 0x e8a9b664c2a654f3
 * Beat 06: 0x 468145e188d76d68
 * Beat 07: 0x c6cdc8efcaa88c4d
 * Beat 08: 0x cf1d0c07a6a84def
 * Beat 09: 0x b634b1785aa61c60
 * Beat 10: 0x 7963ee74b6fd571e
 * Beat 11: 0x c5368d2cf167fbc5
 * Beat 12: 0x 511ab5e16c58eae6
 * Beat 13: 0x 0a5b30f0fc392e73
 * Beat 14: 0x ce17df657f1b2934
 * Beat 15: 0x 6dd935821c80b07b
 * Beat 16: 0x 8c1b3a509033a546
 * Beat 17: 0x bd76e89020afc327
 * Beat 18: 0x e96cf829e270fdfc
 * Beat 19: 0x 6e873acd7b076a04
 * Beat 20: 0x 9cdcb0b7a688a1e2
 * Beat 21: 0x 7e6973631dcaefc4
 * Beat 22: 0x da3fe6258310a293
 * Beat 23: 0x fc540d1f1f08ad4a
 */

.globl digest_sha3_256
digest_sha3_256:
  .zero 32 /* 4 beats, 8 bytes each */
/* Expected digest (big endian):
 * Beat 00: 0x 50b5d09f74a3fb9b
 * Beat 01: 0x 07edc08a62bf546a
 * Beat 02: 0x 143a1ad234fcfef0
 * Beat 03: 0x a386b78a4869191f
 */
