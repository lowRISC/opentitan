/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_BN_RSHI FI Penetration Test
*/
.section .text.start
  /* Load 2x256 bit big_num provided by host into w4 & w31. */
  la      x1, big_num
  li      x2, 4
  li      x3, 31
  bn.lid  x2, 0x00(x1++)
  bn.lid  x3, 0x00(x1)

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  bn.rshi w4, w31, w4 >> 129
  bn.rshi w4, w4, w31 >> 127

  /* Write w4 & w31 back to DEM. */
  li      x2, 4
  li      x3, 31
  la      x1, big_num_out
  bn.sid  x2, 0x000(x1++)
  bn.sid  x3, 0x000(x1)

  ecall

.data
  .balign 32
  .globl big_num
  big_num:
    .zero 64

  .globl big_num_out
  .balign 32
  big_num_out:
    .zero 64
