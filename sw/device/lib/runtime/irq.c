// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/irq.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/uart.h"

#define IRQ_ABI __attribute__((aligned(4), interrupt))

size_t irq_type_scratch_area = 0;
IRQ_ABI void irq_internal_dispatch(void) {
  irq_handler_t handler =
      irq_vtable[irq_type_scratch_area / sizeof(irq_handler_t)];
  uart_send_str("Trampolining to interrupt handler at 0x");
  uart_send_uint((uintptr_t)handler, 32);
  uart_send_str(".\n");

  handler();
  uart_send_str("Interrupt handler done.\n");
}

static void noreturn irq_software_default(void) {
  uart_send_str("Now looping forever.\n");
  while (true) {
    asm volatile("wfi");
  }
}

static void noreturn irq_timer_default(void) {
  uart_send_str("Default timer IRQ triggered!\n");
  uart_send_str("Now looping forever.\n");
  while (true) {
    asm volatile("wfi");
  }
}

static void noreturn irq_external_default(void) {
  uart_send_str("Default external IRQ triggered!\n");
  uart_send_str("Now looping forever.\n");
  while (true) {
    asm volatile("wfi");
  }
}

static void noreturn irq_nmi_default(void) {
  uart_send_str("Default NMI triggered!\n");
  uart_send_str("Now looping forever.\n");
  while (true) {
    asm volatile("wfi");
  }
}

static void dispatch_exception(void) {
  exception_type_t cause = get_exception_cause();
  exception_vtable[cause](cause);
}

irq_handler_t irq_vtable[32] = {
    [kIrqException] = &dispatch_exception,
    [kIrqSoftware] = &irq_software_default,
    [kIrqTimer] = &irq_timer_default,
    [kIrqExternal] = &irq_external_default,
    [kIrqNmi] = &irq_nmi_default,
};

const char *describe_exception(exception_type_t cause) {
  switch (cause) {
    case kMisalignedProgramCounter:
      return "misaligned program counter";
    case kInstructionAccessFault:
      return "instruction access fault";
    case kIllegalInstruction:
      return "illegal instruction";
    case kBreakpoint:
      return "breakpoint";
    case kLoadAccessFault:
      return "load access fault";
    case kStoreAccessFault:
      return "store access fault";
    case kEcallUser:
      return "user-mode ecall";
    case kEcallMachine:
      return "machine-mode ecall";
    default:
      return "unknown exception";
  }
}

static void default_exception_handler(exception_type_t cause) {
  const char *cause_name = describe_exception(cause);
  uint32_t mtval = get_trap_value();
  uart_send_str("Exception: ");
  uart_send_str((char *)cause_name);
  uart_send_str("; mtval = 0x");
  uart_send_uint(mtval, 32);
  uart_send_str("\n");
  uart_send_str("Now looping forever.\n");
  while (true) {
    asm volatile("wfi");
  }
}

exception_handler_t exception_vtable[32] = {
    [kMisalignedProgramCounter] = &default_exception_handler,
    [kInstructionAccessFault] = &default_exception_handler,
    [kIllegalInstruction] = &default_exception_handler,
    [kBreakpoint] = &default_exception_handler,
    [kLoadAccessFault] = &default_exception_handler,
    [kStoreAccessFault] = &default_exception_handler,
    [kEcallUser] = &default_exception_handler,
    [kEcallMachine] = &default_exception_handler};

exception_type_t get_exception_cause(void) {
  uint32_t mcause;
  asm volatile("csrr %0, mcause" : "=r"(mcause));
  return (exception_type_t)(mcause & 31);
}

void set_irq_vector(void *irq_vector) {
  asm volatile("csrw mtvec, %0" ::"r"(irq_vector));
}

uint32_t get_trap_value(void) {
  uint32_t mtval;
  asm volatile("csrr %0, mtval" : "=r"(mtval));
  return mtval;
}

void irq_global_set_enabled(bool enabled) {
  if (enabled) {
    asm volatile("csrsi mstatus, 0x8");
  } else {
    asm volatile("csrci mstatus, 0x8");
  }
}

void irq_set_enabled(irq_type_t type, bool enabled) {
  uint32_t value = 0x1 << type;
  if (enabled) {
    asm volatile("csrs mie, %0" ::"r"(value));
  } else {
    asm volatile("csrc mie, %0" ::"r"(value));
  }
}