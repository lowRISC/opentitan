/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
    Code that checks we correctly handle the %lo(...) and %hi(...) relocs
*/

.data
foo:
  .word 0x1234
bar:
  .word 0x5678

.text
  addi  x2, x0, %lo(foo)
  addi  x3, x0, %lo(bar)
  lw    x4, 0(x2)
  lw    x5, 0(x3)

  /* No matter what addresses foo and bar have, we can be pretty
     certain they're representable in 12 bits (if not, they wouldn't
     fit in DMEM). */
  lui   x6, %hi(bar)

  ecall
