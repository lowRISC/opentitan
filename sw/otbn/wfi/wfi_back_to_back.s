/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

  addi  x2, x0, 0x111
  addi  x3, x0, 0x222
  add   x4, x2, x3
  wfi
  wfi
  wfi
  addi  x2, x0, 0x111
  addi  x3, x0, 0x222

  ecall
