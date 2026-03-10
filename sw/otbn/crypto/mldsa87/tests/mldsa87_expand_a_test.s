/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly expand the polynomials of the A matrix. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _expand_a_r0_s0
  la x3, _expand_a_rho
  addi x4, x0, 0
  addi x5, x0, 0

  /* Sample A[i][j] for 0 <= i, j < 3. */

  loopi 4, 6
    loopi 4, 3
      jal x1, expand_a
      addi x2, x2, 1024
      addi x5, x5, 1
      /* End of loop */
    addi x4, x4, 1
    addi x5, x0, 0
    /* End of loop */

  ecall

.data
.balign 32

_expand_a_rho:
.zero 64

_stack:
.zero 4

.section .scratchpad

_expand_a_r0_s0:
.zero 1024
_expand_a_r0_s1:
.zero 1024
_expand_a_r0_s2:
.zero 1024
_expand_a_r0_s3:
.zero 1024
_expand_a_r1_s0:
.zero 1024
_expand_a_r1_s1:
.zero 1024
_expand_a_r1_s2:
.zero 1024
_expand_a_r1_s3:
.zero 1024
_expand_a_r2_s0:
.zero 1024
_expand_a_r2_s1:
.zero 1024
_expand_a_r2_s2:
.zero 1024
_expand_a_r2_s3:
.zero 1024
_expand_a_r3_s0:
.zero 1024
_expand_a_r3_s1:
.zero 1024
_expand_a_r3_s2:
.zero 1024
_expand_a_r3_s3:
.zero 1024
