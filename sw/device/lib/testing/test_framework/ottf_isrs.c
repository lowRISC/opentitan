// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_isrs.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"

/**
 * These weak symbols (pxCurrentTCB and kTestConfig) enable the OTTF ISRs to be
 * used without the OTTF itself. This enables us to maintain one set of default
 * ISRs for testing, while also enabling writing tests that do not make use of
 * the OTTF. See the `crt_test` in `sw/device/tests/crt_test.c` for an example.
 */
OT_WEAK
void *pxCurrentTCB = NULL;
OT_WEAK
void *kTestConfig = NULL;

OT_WEAK
void ottf_exception_handler(void) {
  uint32_t mcause = ibex_mcause_read();

  switch ((ottf_exc_id_t)(mcause & kIdMax)) {
    case kInstrMisaligned:
      ottf_instr_misaligned_fault_handler();
      break;
    case kInstrAccessFault:
      ottf_instr_access_fault_handler();
      break;
    case kIllegalInstrFault:
      ottf_illegal_instr_fault_handler();
      break;
    case kBreakpoint:
      ottf_breakpoint_handler();
      break;
    case kLoadAccessFault:
      ottf_load_store_fault_handler();
      break;
    case kStoreAccessFault:
      ottf_load_store_fault_handler();
      break;
    case kMachineECall:
      ottf_machine_ecall_handler();
      break;
    case kUserECall:
      ottf_user_ecall_handler();
      break;
    default:
      LOG_INFO("Unknown exception triggered!");
      abort();
  }
}

OT_WEAK
void ottf_instr_misaligned_fault_handler(void) {
  LOG_INFO("Misaligned instruction, mtval holds the fault address.");
  LOG_INFO("MTVAL value is 0x%x", ibex_mtval_read());
  abort();
}

OT_WEAK
void ottf_instr_access_fault_handler(void) {
  LOG_INFO("Instruction access fault, mtval holds the fault address.");
  LOG_INFO("MTVAL value is 0x%x", ibex_mtval_read());
  abort();
}

OT_WEAK
void ottf_illegal_instr_fault_handler(void) {
  LOG_INFO("Illegal instruction fault, mtval shows the faulting instruction.");
  LOG_INFO("MTVAL value is 0x%x", ibex_mtval_read());
  abort();
}

OT_WEAK
void ottf_breakpoint_handler(void) {
  LOG_INFO("Breakpoint triggered, mtval holds the breakpoint address.");
  LOG_INFO("MTVAL value is 0x%x", ibex_mtval_read());
  abort();
}

OT_WEAK
void ottf_load_store_fault_handler(void) {
  LOG_INFO("Load/Store fault, mtval holds the fault address.");
  LOG_INFO("MTVAL value is 0x%x", ibex_mtval_read());
  abort();
}

OT_WEAK
void ottf_machine_ecall_handler(void) {
  LOG_INFO("Machine-mode environment call (syscall).");
  abort();
}

OT_WEAK
void ottf_user_ecall_handler(void) {
  LOG_INFO("User-mode environment call (syscall).");
  abort();
}

OT_WEAK
void ottf_software_isr(void) {
  LOG_INFO("Software IRQ triggered!");
  abort();
}

OT_WEAK
void ottf_timer_isr(void) {
  LOG_INFO("Timer IRQ triggered!");
  abort();
}

OT_WEAK
void ottf_external_isr(void) {
  LOG_INFO("External IRQ triggered!");
  abort();
}
