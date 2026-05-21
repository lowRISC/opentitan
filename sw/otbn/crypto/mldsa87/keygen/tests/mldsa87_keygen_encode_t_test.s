/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that the we can correctly round and encode the T{0,1} vectors. */

.section .text.start

main:
  la x31, _stack
  bn.xor w31, w31, w31

  la x2, _params
  bn.lid x0, 0(x2)
  bn.wsrw MOD, w0

  la x2, _encode_t_t0_share0
  la x3, _encode_t_t0_share1
  la x4, _encode_t_t0_enc
  la x5, _encode_t_t1_enc
  la x6, _encode_t_slot0
  la x7, _encode_t_slot1
  jal x1, encode_t

  ecall

.data
.balign 32

_encode_t_t0_enc:
.zero 3328
_encode_t_t1_enc:
.zero 2560

_encode_t_slot0:
.zero 1024
_encode_t_slot1:
.zero 1024

_params:
.word 0x007fe001 /* q */
.word 0xfc7fdfff /* mu */
.word 0x0000a3fa /* n^-1 * R^3 mod q */
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

_stack:
.zero 256

.section .scratchpad

_encode_t_t0_share0:
.zero 1024
_encode_t_t1_share0:
.zero 1024
_encode_t_t2_share0:
.zero 1024
_encode_t_t3_share0:
.zero 1024
_encode_t_t4_share0:
.zero 1024
_encode_t_t5_share0:
.zero 1024
_encode_t_t6_share0:
.zero 1024
_encode_t_t7_share0:
.zero 1024

_encode_t_t0_share1:
.zero 1024
_encode_t_t1_share1:
.zero 1024
_encode_t_t2_share1:
.zero 1024
_encode_t_t3_share1:
.zero 1024
_encode_t_t4_share1:
.zero 1024
_encode_t_t5_share1:
.zero 1024
_encode_t_t6_share1:
.zero 1024
_encode_t_t7_share1:
.zero 1024
