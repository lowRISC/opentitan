/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Call a subroutine directly. */

main:
  addi    x11, x0, 5

  jal     x1, subroutine

  ecall

subroutine:
  addi    x11, x11, -1
  jalr    x0, x1, 0
