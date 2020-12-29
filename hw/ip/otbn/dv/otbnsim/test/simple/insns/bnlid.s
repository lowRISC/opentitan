/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

  /*
    Check that bn.lid (wide data loading) loads its data as a 256-bit
    little-endian value.

    This should load 0x1f1e...0100 (see comment in .data section) from address
    0x0 into w0.
  */
  bn.lid    x0, 0(x0)

  /*
    Checks for increment behaviour. First, incrementing <grd>: set x2 to 1,
    then load-with-increment (from address 0x20, to distinguish from the
    previous load). We should have data from 0x20 in w1 and x2 should equal 2.
  */
  addi      x2, x0, 1
  bn.lid    x2++, 32(x0)

  /*
    Check wrapping and incrementing on the grd side. Set x3 to 32+2 and load
    with increment from address 0x40. We should get data from 0x40 in w2 and x3
    should equal 3
  */
  addi      x3, x0, 34
  bn.lid    x3++, 64(x0)

  ecall


.section .data
  /*
    Since each .word is a 32-bit value stored little-endian, this is 32 bytes
    laid out in memory as 00, 01, 02, .., 1f. If loaded 256-bit little endian,
    the result will be 0x1f1e1d...020100.
  */
  .word 0x03020100
  .word 0x07060504
  .word 0x0b0a0908
  .word 0x0f0e0d0c
  .word 0x13121110
  .word 0x17161514
  .word 0x1b1a1918
  .word 0x1f1e1d1c
  /* The following words are carry on the count, so the next is 0x3f3e...2120
     etc. */
  /* Address 0x20: */
  .word 0x23222120
  .word 0x27262524
  .word 0x2b2a2928
  .word 0x2f2e2d2c
  .word 0x33323130
  .word 0x37363534
  .word 0x3b3a3938
  .word 0x3f3e3d3c
  /* Address 0x40: */
  .word 0x43424140
  .word 0x47464544
  .word 0x4b4a4948
  .word 0x4f4e4d4c
  .word 0x53525150
  .word 0x57565554
  .word 0x5b5a5958
  .word 0x5f5e5d5c
