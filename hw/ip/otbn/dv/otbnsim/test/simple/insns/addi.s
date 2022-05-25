/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
    Simple tests of the addi instruction

    This test also uses a comment syntax that broke the parser in a
    previous version of otbn_as.py: if editing it, keep the block
    comments on the same lines as instructions to keep that test in
    place.

*/

  addi    x10, x0, 1

  addi    x2, x0, 1   /* x2 = 0 + 1 = 1 */
  addi    x3, x2, 1   /* x3 = 1 + 1 = 2 */
  addi    x4, x0, -1  /* x4 = 0 + (-1) = 0xffffffff */
  addi    x5, x3, -1  /* x5 = 2 + (-1) = 1 */
  addi    x6, x4, 10  /* x6 = -1 + 10 = 9 */

  ecall
