// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/handler.h"

#include "sw/device/lib/base/log.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/common.h"
#include "sw/device/lib/uart.h"

/**
 * Return value of mtval
 */
static uint32_t get_mtval(void) {
  uint32_t mtval;
  asm volatile("csrr %0, mtval" : "=r"(mtval) : :);
  return mtval;
}

// Below functions are default weak exception handlers meant to be overriden
__attribute__((weak)) void handler_exception(void) {
  uint32_t mcause;
  exc_id_t exc_cause;

  asm volatile("csrr %0 , mcause" : "=r"(mcause) : :);
  exc_cause = (exc_id_t)(mcause & kIdMax);

  switch (exc_cause) {
    case kInstMisa:
      handler_instr_acc_fault();
      break;
    case kInstAccFault:
      handler_instr_acc_fault();
      break;
    case kInstIllegalFault:
      handler_instr_ill_fault();
      break;
    case kBkpt:
      handler_bkpt();
      break;
    case kLoadAccFault:
      handler_lsu_fault();
      break;
    case kStrAccFault:
      handler_lsu_fault();
      break;
    case kECall:
      handler_ecall();
      break;
    default:
      while (1) {
      };
  }
}

__attribute__((weak)) void handler_irq_software(void) {
  LOG_INFO("Software IRQ triggered!");
  while (1) {
  }
}

__attribute__((weak)) void handler_irq_timer(void) {
  LOG_INFO("Timer IRQ triggered!");
  while (1) {
  }
}

__attribute__((weak)) void handler_irq_external(void) {
  LOG_INFO("External IRQ triggered!");
  while (1) {
  }
}

__attribute__((weak)) void handler_instr_acc_fault(void) {
  LOG_ERROR("Instruction access fault at address %p", get_mtval());
}

__attribute__((weak)) void handler_instr_ill_fault(void) {
  LOG_ERROR("Illegal instruction fault at address %p", get_mtval());
}

__attribute__((weak)) void handler_bkpt(void) {
  LOG_INFO("Breakpoint triggered at address %p", get_mtval());
}

__attribute__((weak)) void handler_lsu_fault(void) {
  LOG_ERROR("Load/store unit fault at address %p", get_mtval());
}

__attribute__((weak)) void handler_ecall(void) {
  LOG_INFO("Environment call encountered");
  while (1) {
  }
}
