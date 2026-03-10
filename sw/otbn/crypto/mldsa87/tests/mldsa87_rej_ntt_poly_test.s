/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test that we can correctly sample a polynomial in the NTT domain. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _rej_ntt_poly_output
  la x3, _rej_ntt_poly_rho
  jal x1, rej_ntt_poly

  ecall

.data
.balign 32

_rej_ntt_poly_rho:
.zero 64

_rej_ntt_poly_output:
.zero 1024

_stack:
.zero 4
