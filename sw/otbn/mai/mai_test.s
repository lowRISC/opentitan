/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * A simple program showcasing how to use the MAI and testing its operations.
 *
 * Each operation is tested separately in its own subroutine:
 *   - B2A followed by A2B, which must return the secret unchanged.
 *   - secAdd, a Boolean-masked addition of two operands.
 */
.global main

.text

main:
  bn.xor w31, w31, w31

  /* Load the modulus used by the MAI operations. */
  li x2, 30
  la x3, mod32
  bn.lid x2, 0(x3)
  bn.wsrw MOD, w30

  jal x1, _test_b2a_a2b
  jal x1, _test_secadd

  /* TODO: add secAddMod test */

  ecall

/**
 * Tests the B2A and A2B conversions.
 *
 * Boolean-masks the secrets in DMEM, converts it to the arithmetically masked
 * domain and back, then stores the unmasked secrets to `result`. On
 * success the stored value equals the original secrets.
 */
_test_b2a_a2b:
  /* Load the secret to be converted from DMEM into w0. */
  li x2, 0
  la x3, secret
  bn.lid x2, 0(x3)

  /* Add a Boolean mask to the secrets. */
  bn.wsrr w2, URND
  bn.xor w1, w0, w2

  /* Write the Boolean masked shares to the WSRs. */
  jal x1, _poll_ready
  bn.wsrw MAI_IN0_S0, w1
  bn.wsrw MAI_IN0_S1, w2

  /* Start the B2A conversion. */
  jal x1, _poll_busy
  li x10, 0x21
  csrrw x0, MAI_CTRL, x10
  jal x1, _poll_busy

  /* Retrieve the arithmetically-masked shares. */
  bn.wsrr w20, MAI_RES_S0
  bn.wsrr w21, MAI_RES_S1

  /* Write the arithmetically-masked shares to the WSRs. */
  jal x1, _poll_ready
  bn.wsrw MAI_IN0_S0, w20
  bn.wsrw MAI_IN0_S1, w21

  /* Start the A2B conversion. */
  jal x1, _poll_busy
  li x10, 0x17
  csrrw x0, MAI_CTRL, x10
  jal x1, _poll_busy

  /* Read the Boolean masked shares and unmask the secret. */
  bn.wsrr w22, MAI_RES_S0
  bn.wsrr w23, MAI_RES_S1
  bn.xor w24, w22, w23

  /* Store the recovered secret. */
  li x2, 24
  la x3, result
  bn.sid x2, 0(x3)
  ret

/**
 * Tests the secAdd operation.
 *
 * Loads two operands from DMEM, masks them Boolean, computes their arithmetic sum, and stores the
 * unmasked sum to `result_secadd`.
 */
_test_secadd:
  li x2, 0
  la x3, operand_a
  bn.lid x2, 0(x3)            /* w0 = x */
  li x2, 3
  la x3, operand_b
  bn.lid x2, 0(x3)            /* w3 = y */

  li x10, 0x2f               /* CTRL: secAdd + start */

  /* Add a Boolean mask to both operands: (x ^ r, r) and (y ^ s, s). */
  bn.wsrr w4, URND
  bn.xor w5, w0, w4
  bn.wsrr w6, URND
  bn.xor w7, w3, w6

  /* Write the masked shares to the IN0 and IN1 WSRs. */
  jal x1, _poll_ready
  bn.wsrw MAI_IN0_S0, w5
  bn.wsrw MAI_IN0_S1, w4
  bn.wsrw MAI_IN1_S0, w7
  bn.wsrw MAI_IN1_S1, w6

  /* Start the operation and wait for it to complete. */
  jal x1, _poll_busy
  csrrw x0, MAI_CTRL, x10
  jal x1, _poll_busy

  /* Read the result shares and unmask the result. */
  bn.wsrr w8, MAI_RES_S0
  bn.wsrr w9, MAI_RES_S1
  bn.xor w10, w8, w9

  /* Store the unmasked result. */
  la x11, result_secadd
  li x2, 10
  bn.sid x2, 0(x11)

  ret

/**
 * Polls the MAI_STATUS busy bit until the MAI is no longer busy.
 * Clobbers: x2
 */
_poll_busy:
  csrrs x2, MAI_STATUS, x0
  andi x2, x2, 0x1
  bne x2, x0, _poll_busy
  ret

/**
 * Polls the MAI_STATUS ready bit until the MAI is ready for inputs.
 * Clobbers: x2
 */
_poll_ready:
  csrrs x2, MAI_STATUS, x0
  andi x2, x2, 0x2
  beq x2, x0, _poll_ready
  ret

.section .data

/* The secret to be converted by the B2A/A2B test. */
.balign 32
.globl secret
secret:
  .zero 32

/* The two operands added by the secAdd and secAddMod tests. */
.balign 32
.globl operand_a
operand_a:
  .zero 32

.balign 32
.globl operand_b
operand_b:
  .zero 32

/* The recovered secret of the B2A/A2B test. */
.balign 32
.globl result
result:
  .zero 32

/* The unmasked sum produced by the secAdd test. */
.balign 32
.globl result_secadd
result_secadd:
  .zero 32

/*
  mod32 = 8380417
*/
.balign 32
mod32:
  .word 0x007fe001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
