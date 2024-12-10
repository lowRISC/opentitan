/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    OBTN.CHAR_BN_SEL FI Penetration Test
*/
.section .text.start
  /* Load 2x256 bit big_num provided by host into w0 & w1. */
  la      x1, big_num
  li      x2, 0
  li      x3, 1
  bn.lid  x2, 0x00(x1++)
  bn.lid  x3, 0x00(x1)

  /* Add with carry: big_num = big_num + big_num. */
  bn.addc w0, w0, w0

  /* If C is set, these four instructions swap the content of w0 and w1. */
  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  /* Repeat 250 times. */
  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C

  bn.sel  w2, w1, w0, C
  bn.sel  w3, w0, w1, C
  bn.sel  w1, w3, w2, C
  bn.sel  w0, w2, w3, C


  /* Write w0 & w1 back to DEM. */
  li      x2, 0
  li      x3, 1
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
