/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Underflow call stack for grs and bad WDR index for grd

  One thing that might go wrong is if that the big-number register file
  responds with X's to the BN.MOVR instruction that's supposed to trigger the
  error. This is a little awkward to avoid: firstly, we need a defined
  big-number register despite underflowing the call stack. Secondly, we need to
  ensure that this register has known data.
*/
  /*
    Ensure that a read from the empty call stack gives zero (as well as a stack
    underflow error) by clearing all the entries.
  */
  loopi 8, 1
    addi x1, x0, 0
  loopi 8, 1
    addi x0, x1, 0

  /*
    Zero out w0, which will be selected by x1
  */
  bn.xor w0, w0, w0

  addi    x2, x0, 100
  bn.movr x2, x1
