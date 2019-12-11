// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.extern irq_type_scratch_area
.extern irq_internal_dispatch

#define HANDLER_STUB(label, type)     \
  label:                              \
    sw s0, -4(sp);                    \
    sw s1, -8(sp);                    \
    li s0, type;                      \
    sw s0, irq_type_scratch_area, s1; \
    lw s0, -4(sp);                    \
    lw s1, -8(sp);                    \
    j irq_internal_dispatch;

HANDLER_STUB(handle_irq_exception, 0x0)
HANDLER_STUB(handle_irq_software, 0x0c)
HANDLER_STUB(handle_irq_timer, 0x1c)
HANDLER_STUB(handle_irq_external, 0x2c)
HANDLER_STUB(handle_irq_nmi, 0x7c)

exception_handlers:
  .section .vectors
  .global vector_handlers

  // Exception handler.
  .org 0x0
  j handle_irq_exception

  // Software interrupt handler.
  .org 0x0c
  j handle_irq_software

  // Timer interrupt handler.
  .org 0x1c
  j handle_irq_timer

  // External interrupt handler.
  .org 0x2c
  j handle_irq_external

  // NMI handler.
  .org 0x7c
  j handle_irq_nmi
