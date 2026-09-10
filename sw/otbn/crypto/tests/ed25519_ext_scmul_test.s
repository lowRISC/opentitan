/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  bn.xor w31, w31, w31

  /* Set up for field arithmetic in preparation for scalar multiplication and
     point addition.
       MOD <= p
       w19 <= 19 */
  jal x1, fe_init

  /* Initialize curve parameter d.
       w29 <= dmem[d] = (-121665/121666) mod p */
  li x2, 29
  la x3, _ed25519_ext_scmul_d
  bn.lid x2, 0(x3)

  /* Precompute (2*d) mod p in preparation for scalar multiplication.
       w29 <= (w29 + w29) mod p = (2 * d) mod p */
  bn.addm w29, w29, w29

  /* Load shared scalar.
       w2 <= s0
       w4 <= s1. */
  li x2, 2
  la x3, _ed25519_ext_scmul_a_share0
  bn.lid x2, 0(x3)
  li x2, 4
  la x3, _ed25519_ext_scmul_a_share1
  bn.lid x2, 0(x3)

  /* Load curve point coordinates.
       [w9:w6] <= (B.X, B.Y, B.Z, B.T). */
  li x2, 6
  la x3, _ed25519_ext_scmul_x1
  bn.lid x2++, 0(x3)
  bn.lid x2++, 32(x3)
  bn.lid x2++, 64(x3)
  bn.lid x2++, 96(x3)

  /* Calculate [s]B and convert to affine coordiantes. */
  jal x1, ext_scmul_sca
  jal x1, ext_to_affine

  /* Store result in DMEM. */
  li x2, 10
  la x3, _ed25519_ext_scmul_x2
  bn.sid x2++, 0(x3)
  bn.sid x2++, 32(x3)

  ecall

.data
.balign 32

_ed25519_ext_scmul_a_share0:
.zero 32
_ed25519_ext_scmul_a_share1:
.zero 32

_ed25519_ext_scmul_x1:
.zero 32
_ed25519_ext_scmul_y1:
.zero 32
_ed25519_ext_scmul_z1:
.zero 32
_ed25519_ext_scmul_t1:
.zero 32

_ed25519_ext_scmul_x2:
.zero 32
_ed25519_ext_scmul_y2:
.zero 32

_ed25519_ext_scmul_d:
.word 0x135978a3
.word 0x75eb4dca
.word 0x4141d8ab
.word 0x00700a4d
.word 0x7779e898
.word 0x8cc74079
.word 0x2b6ffe73
.word 0x52036cee
