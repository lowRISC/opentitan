/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Call a subroutine through a function pointer. */

main:
  addi    x11, x0, 5

  addi    x10, x0, 0x10
  jalr    x1, x10, 0

  ecall

subroutine:
  addi    x11, x11, -1
  jalr    x0, x1, 0
