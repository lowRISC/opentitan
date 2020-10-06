/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    An example of the pseudo-operations supported by the OTBN ISA
*/

nop_example:
    /* NOP is a no-op, and expands to addi x0, x0, 0 */
    nop

ret_example:
    /* RET is a return and expands to jalr x0, x1, 0 */
    ret

li_example:
    /* LI is a bit more complicated. With a small immediate, it turns
       into just addi */
    li x2, 1230
    li x2, -123
    li x2, 2272

    /* With a big immediate which happens to have nothing set in the
       lower 20 bits, it turns into just a LUI */
    li x2, 1048576
    li x2, -0x800000

    /* With a big immediate in general, we need 2 instructions.
       Firstly, a LUI to set up the upper bits, then an ADDI to sort out
       the lower ones. */
    li x2, 0x10000042

    li x2, 123456789
    li x2, 0x7fffffff
