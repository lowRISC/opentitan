/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Test we can correctly modular reduce 512-bit and 768-bit numbers. */

.section .text.start

main:
  bn.xor w31, w31, w31

  /* [w15:w14] <= mu, MOD <= L. */
  jal x1, sc_init

  /*
   * Test 1: 512-bit modular reduction.
   */

  /* [w17:w16] <= dmem[_sc_reduce_512_x] = x. */
  li x2, 16
  la x3, _sc_reduce_512_x
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)

  /* w18 <= x mod L. */
  jal x1, sc_reduce

  /* dmem[_sc_reduce_512_y] <= w18 = x mod L. */
  la x2, _sc_reduce_512_y
  li x3, 18
  bn.sid x3, 0(x2)

  /*
   * Test 2: 768-bit modular reduction.
   */

  /* [w22:w20] <= dmem[_sc_reduce_768_x] = x. */
  li x2, 20
  la x3, _sc_reduce_768_x
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)
  bn.lid x2++, 64(x3)

  /* w18 <= x mod L. */
  jal x1, sc_reduce_768

  /* dmem[_sc_reduce_768_y] <= w18 = x mod L. */
  la x2, _sc_reduce_768_y
  li x3, 18
  bn.sid x3, 0(x2)

  ecall

.data
.balign 32

_sc_reduce_512_x:
.zero 64
_sc_reduce_512_y:
.zero 32

_sc_reduce_768_x:
.zero 96
_sc_reduce_768_y:
.zero 32
