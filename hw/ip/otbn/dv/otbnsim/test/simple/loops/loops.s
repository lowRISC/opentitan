/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

  /* A basic example of using loop / loopi instructions to increment a
     counter

     In C-like pseudo-code, this would be:

       x2 = 0;
       x3 = 3;

       for (int i = 0; i < 4; ++i) {
         x2 += 10;
         for (int j = 0; j < x3; ++j) {
           x2 += 1;
         }
       }

     The outer loop executes 4 times and the inner loop executes 3 times
     on each iteration, so we increment x2 by 4*(10 + 3*1) = 52.

   */
  addi    x2, x0, 0
  addi    x3, x0, 3

  loopi  4, 4
   addi   x2, x2, 10
   loop   x3, 1
    addi   x2, x2, 1
   nop

  ecall
