/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly sample a polynomials with coefficients in
   {-1, 0, 1} and Hamming weight TAU=60. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _sample_in_ball_c
  la x3, _sample_in_ball_rho
  jal x1, sample_in_ball

  ecall

.data
.balign 32

_sample_in_ball_rho:
.zero 64
_sample_in_ball_c:
.zero 1024

_stack:
.zero 4
