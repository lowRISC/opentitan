/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    Checks for li support

    This is really a test of the assembler, which is supposed to expand the li
    pseudo-instruction into addi/lui as necessary. Of course, checking that the
    expansion was correct is a little difficult, unless you can run the
    generated instructions... which is what we can do for ISS testing. So the
    checks seem to fit quite well here.

*/
  li x2, 1230
  li x3, -123
  li x4, 2272

  /* Big immediates that can be done with a single LUI */
  li x5, 1048576
  li x6, -0x800000

  /* Other big immediates */
  li x7, 6368
  li x8, 0x10000042
  li x9, 123456789
  li x10, 0x7fffffff

  /* We also allow immediates in the range [2^31, 2^32-1] (which could
     equally have been specified as negative constants) because
     sometimes this is more useful for "magic hex numbers" */
  li x11, 0xffffffff
  li x12, 0x80000000
  li x13, 0x80000001

  ecall
