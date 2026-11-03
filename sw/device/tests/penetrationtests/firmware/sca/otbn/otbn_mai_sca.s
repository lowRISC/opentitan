/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 * OTBN MAI (Masking Accelerator Interface) SCA Test
 *
 * Adapted from mai_test.s and mai_gadgets.s for hardware TVLA evaluation.
 * All inputs and outputs in DMEM are pre-masked / post-unmasked on Ibex outside
 * the SCA trigger window, and DMEM/WSR accesses between shares are separated by
 * dummy zero loads/stores and bn.xor w31, w31, w31 barriers so that TVLA tests
 * the MAI hardware block itself without software-induced share transitions.
 */

.section .text.start
.globl main
main:
  /* Initialize zero register and helper pointers. */
  bn.xor  w31, w31, w31
  li      x31, 31
  la      x8, dmem_zero

  /* Load modulus q = 0x007fe001 into MOD WSR. */
  la      x2, mod32
  bn.lid  x31, 0(x2)
  bn.wsrw MOD, w31
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31

  /* Read mode from DMEM:
   *   0 = B2A->A2B + SecAdd (full mai_test)
   *   1 = B2A only
   *   2 = A2B only
   *   3 = SecAdd only
   */
  la      x2, mode
  lw      x3, 0(x2)
  li      x4, 1
  beq     x3, x4, _run_only_b2a
  li      x4, 2
  beq     x3, x4, _run_only_a2b
  li      x4, 3
  beq     x3, x4, _run_only_secadd

  /* Default (mode 0): run B2A->A2B followed by SecAdd. */
  jal     x1, _test_b2a_a2b
  jal     x1, _test_secadd
  ecall

_run_only_b2a:
  jal     x1, _test_only_b2a
  ecall

_run_only_a2b:
  jal     x1, _test_only_a2b
  ecall

_run_only_secadd:
  jal     x1, _test_secadd
  ecall

/**
 * Test B2A followed by A2B conversion in MAI hardware.
 */
_test_b2a_a2b:
  /* Load Boolean shares in0_s0 -> w0, in0_s1 -> w1 with DMEM bus clearing. */
  li      x10, 0
  li      x11, 1
  la      x9, in0_s0
  bn.lid  x10, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, in0_s1
  bn.lid  x11, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  /* Run B2A conversion in MAI hardware. */
  jal     x1, sec_b2a_8x32

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  /* Run A2B conversion in MAI hardware. */
  jal     x1, sec_a2b_8x32

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  /* Store output shares w0 -> res_b2a_a2b_s0, w1 -> res_b2a_a2b_s1. */
  la      x9, res_b2a_a2b_s0
  bn.sid  x10, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, res_b2a_a2b_s1
  bn.sid  x11, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31

  /* Clear working registers. */
  bn.xor  w0, w0, w0
  bn.xor  w31, w31, w31
  bn.xor  w1, w1, w1
  bn.xor  w31, w31, w31

  ret

/**
 * Test B2A conversion only in MAI hardware.
 */
_test_only_b2a:
  li      x10, 0
  li      x11, 1
  la      x9, in0_s0
  bn.lid  x10, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, in0_s1
  bn.lid  x11, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  jal     x1, sec_b2a_8x32

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  la      x9, res_b2a_a2b_s0
  bn.sid  x10, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, res_b2a_a2b_s1
  bn.sid  x11, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31

  bn.xor  w0, w0, w0
  bn.xor  w31, w31, w31
  bn.xor  w1, w1, w1
  bn.xor  w31, w31, w31

  ret

/**
 * Test A2B conversion only in MAI hardware.
 */
_test_only_a2b:
  li      x10, 0
  li      x11, 1
  la      x9, in0_s0
  bn.lid  x10, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, in0_s1
  bn.lid  x11, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  jal     x1, sec_a2b_8x32

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  la      x9, res_b2a_a2b_s0
  bn.sid  x10, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, res_b2a_a2b_s1
  bn.sid  x11, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31

  bn.xor  w0, w0, w0
  bn.xor  w31, w31, w31
  bn.xor  w1, w1, w1
  bn.xor  w31, w31, w31

  ret

/**
 * Test SecAdd operation in MAI hardware.
 */
_test_secadd:
  /* Load Boolean shares in1_s0 -> w0, in1_s1 -> w1, in2_s0 -> w2, in2_s1 -> w3. */
  li      x10, 0
  li      x11, 1
  li      x12, 2
  li      x13, 3
  la      x9, in1_s0
  bn.lid  x10, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, in1_s1
  bn.lid  x11, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, in2_s0
  bn.lid  x12, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, in2_s1
  bn.lid  x13, 0(x9)
  bn.lid  x31, 0(x8)
  bn.xor  w31, w31, w31

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  /* Run SecAdd in MAI hardware. */
  jal     x1, sec_add_8x32

  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop
  nop

  /* Store output shares w0 -> res_secadd_s0, w1 -> res_secadd_s1. */
  la      x9, res_secadd_s0
  bn.sid  x10, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31
  la      x9, res_secadd_s1
  bn.sid  x11, 0(x9)
  bn.sid  x31, 0(x8)
  bn.xor  w31, w31, w31

  /* Clear working registers. */
  bn.xor  w0, w0, w0
  bn.xor  w31, w31, w31
  bn.xor  w1, w1, w1
  bn.xor  w31, w31, w31
  bn.xor  w2, w2, w2
  bn.xor  w31, w31, w31
  bn.xor  w3, w3, w3
  bn.xor  w31, w31, w31

  ret

.data
.balign 32

.globl mod32
mod32:
  .word 0x007fe001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

.globl dmem_zero
.balign 32
dmem_zero:
  .zero 32

.globl in0_s0
.balign 32
in0_s0:
  .zero 32

.globl in0_s1
.balign 32
in0_s1:
  .zero 32

.globl in1_s0
.balign 32
in1_s0:
  .zero 32

.globl in1_s1
.balign 32
in1_s1:
  .zero 32

.globl in2_s0
.balign 32
in2_s0:
  .zero 32

.globl in2_s1
.balign 32
in2_s1:
  .zero 32

.globl res_b2a_a2b_s0
.balign 32
res_b2a_a2b_s0:
  .zero 32

.globl res_b2a_a2b_s1
.balign 32
res_b2a_a2b_s1:
  .zero 32

.globl res_secadd_s0
.balign 32
res_secadd_s0:
  .zero 32

.globl res_secadd_s1
.balign 32
res_secadd_s1:
  .zero 32

.globl mode
.balign 4
mode:
  .zero 4
