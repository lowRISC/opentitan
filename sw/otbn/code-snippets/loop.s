/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    An example of how hardware loops work in OTBN
*/

    /* The basic loop instruction (running 2 instructions 3 times) */
    li  x2, 3
    li  x3, 0

    loop x2, 2
    addi x3, x3, 2
    addi x3, x3, -1

    /* At this point, we've incremented x3 by 2-1 = 1 on each of three
       loop iterations, so x3 should equal 3. */

    loopi 5, 1
    addi x3, x3, -3

    /* Now we've run a loop that decrements x3 by 3 on each of
       five loop iterations, so it should now equal 3-15 = -12. */

    loop x2, 3
    loopi 4, 1
    addi x3, x3, 2
    nop

    /* The nested loop runs 3 * 4 times, incrementing by 2 each
       iteration. So x3 should now equal -12 + 2*12 = 12. */

    ecall
