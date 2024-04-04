/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
    Checks for "la" pseudo-instruction support
*/
.data
foo:
  .word 0x1234

bar:
  .word 0x5678

.text
  la x2, foo
  la x3, bar
  lw x4, 0(x2)
  lw x5, 0(x3)
  ecall
