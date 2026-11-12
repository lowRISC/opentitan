/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * A simple program showcasing how to use the MAI and testing its operations.
 *
 * Each operation is tested separately in its own subroutine:
 *   - B2A followed by A2B, which must return the secret unchanged.
 *   - secAdd, a Boolean-masked addition of two operands.
 *   - B2A with a small modulus, so that some of its random masks are zero.
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
  jal x1, _test_b2a_zero_mask

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
  jal x1, _poll_ready_for_inputs
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
  jal x1, _poll_ready_for_inputs
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
  jal x1, _poll_ready_for_inputs
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
 * Tests the B2A conversion with a zero mask.
 *
 * B2A draws a random mask below the modulus for each element. With the
 * modulus 3 one mask in three is zero. The test converts 128 elements, so
 * the probability that none of the masks is zero is (2/3)^128.
 *
 * Each round converts the secrets to arithmetic shares and back. Both
 * arithmetic shares must be below the modulus and the round trip must return
 * the secrets. Every deviation sets bits in `result_zero_mask`, which is zero
 * on success.
 */
_test_b2a_zero_mask:
  /* Load the modulus 3. */
  li x2, 30
  la x3, mod3
  bn.lid x2, 0(x3)
  bn.wsrw MOD, w30

  /* Load the secrets into w0 and clear the deviations in w25. */
  li x2, 0
  la x3, secret_mod3
  bn.lid x2, 0(x3)
  bn.xor w25, w25, w25

  li x10, 0x21               /* CTRL: B2A + start */
  li x11, 0x17               /* CTRL: A2B + start */

  loopi 16, 27
    /* Add a Boolean mask to the secrets and convert them with B2A. */
    bn.wsrr w2, URND
    bn.xor w1, w0, w2
    jal x1, _poll_ready_for_inputs
    bn.wsrw MAI_IN0_S0, w1
    bn.wsrw MAI_IN0_S1, w2
    jal x1, _poll_busy
    csrrw x0, MAI_CTRL, x10
    jal x1, _poll_busy
    bn.wsrr w20, MAI_RES_S0
    bn.wsrr w21, MAI_RES_S1

    /* A share below the modulus is not changed by a modular reduction. */
    bn.addvm.8S w22, w20, w31
    bn.xor w22, w22, w20
    bn.or w25, w25, w22
    bn.addvm.8S w22, w21, w31
    bn.xor w22, w22, w21
    bn.or w25, w25, w22

    /* Convert back with A2B and compare with the secrets. */
    jal x1, _poll_ready_for_inputs
    bn.wsrw MAI_IN0_S0, w20
    bn.wsrw MAI_IN0_S1, w21
    jal x1, _poll_busy
    csrrw x0, MAI_CTRL, x11
    jal x1, _poll_busy
    bn.wsrr w22, MAI_RES_S0
    bn.wsrr w23, MAI_RES_S1
    bn.xor w22, w22, w23
    bn.xor w22, w22, w0
    bn.or w25, w25, w22

  /* Store the deviations. */
  li x2, 25
  la x3, result_zero_mask
  bn.sid x2, 0(x3)
  ret

/**
 * Polls the MAI_STATUS BUSY bit until the MAI is no longer busy.
 * Clobbers: x2
 */
_poll_busy:
  csrrs x2, MAI_STATUS, x0
  andi x2, x2, 0x1
  bne x2, x0, _poll_busy
  ret

/**
 * Polls the MAI_STATUS INPUT_READY bit until the MAI is ready for inputs.
 * Clobbers: x2
 */
_poll_ready_for_inputs:
  csrrs x2, MAI_STATUS, x0
  andi x2, x2, 0x2
  beq x2, x0, _poll_ready_for_inputs
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
 * The deviations found by the B2A zero-mask test. All ones until the test has
 * stored its result.
 */
.balign 32
.globl result_zero_mask
result_zero_mask:
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff

/* The secrets of the B2A zero-mask test, each below the modulus 3. */
.balign 32
secret_mod3:
  .word 0x00000000
  .word 0x00000001
  .word 0x00000002
  .word 0x00000001
  .word 0x00000002
  .word 0x00000000
  .word 0x00000002
  .word 0x00000001

.balign 32
mod3:
  .word 0x00000003
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

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
