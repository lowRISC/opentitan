// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.extern handler_exception
.extern handler_irq_software
.extern handler_irq_timer
.extern handler_irq_external

exception_handlers:
  .section .vectors, "ax"
  .global vector_handlers

  // exception handler
  .org 0x0
  jal x0, handler_exception

  // software interrupt handler
  .org 0x0c
  jal x0, handler_irq_software

  // timer interrupt handler
  .org 0x1c
  jal x0, handler_irq_timer

  // external interrupt handler
  .org 0x2c
  jal x0, handler_irq_external
