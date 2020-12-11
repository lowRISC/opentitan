/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

  /* An example that overflows the loop stack. We check the depth
     exactly by running an 8-deep loop first (which should work) and
     then 9 deep, which should fail.

   */
  addi  x2, x0, 0
  addi  x3, x0, 0
  addi  x4, x0, 4

  loopi 1, 15
   loopi 1, 13
    loopi 1, 11
     loopi 1, 9
      loopi 1, 7
       loopi 1, 5
        loopi 1, 3
         loopi 1, 1
          addi x2, x2, 1
         nop
        nop
       nop
      nop
     nop
    nop
   nop

  loopi 1, 17
   loopi 1, 15
    loopi 1, 13
     loopi 1, 11
      loopi 1, 9
       loopi 1, 7
        loopi 1, 5
         loopi 1, 3
          loopi 1, 1
           addi x3, x3, 1
          nop
         nop
        nop
       nop
      nop
     nop
    nop
   nop

  /* We shouldn't get here */
  addi  x4, x0, 40
  ecall
