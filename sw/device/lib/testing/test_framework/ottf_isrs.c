// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_isrs.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"

// Fault reasons from
// https://riscv.org/wp-content/uploads/2017/05/riscv-privileged-v1.10.pdf
static const char *exception_reason[] = {
    "Instruction Misaligned",
    "Instruction Access",
    "Illegal Instruction",
    "Breakpoint",
    "Load Address Misaligned",
    "Load Access Fault",
    "Store Address Misaligned",
    "Store Access Fault",
    "U-mode Ecall",
    "S-mode Ecall",
    "Reserved",
    "M-mode Ecall",
    "Instruction Page Fault",
    "Load Page Fault",
    "Reserved",
    "Store Page Fault",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
    "Reserved",
};

static void generic_fault_print(const char *reason, uint32_t mcause) {
  uint32_t mepc = ibex_mepc_read();
  uint32_t mtval = ibex_mtval_read();
  LOG_ERROR("FAULT: %s. MCAUSE=%08x MEPC=%08x MTVAL=%08x", reason, mcause, mepc,
            mtval);
}

static void generic_fault_handler(void) {
  uint32_t mcause = ibex_mcause_read();
  generic_fault_print(exception_reason[mcause & kIdMax], mcause);
  abort();
}

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
      generic_fault_handler();
  }
}

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_instr_misaligned_fault_handler(void);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_instr_access_fault_handler(void);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_illegal_instr_fault_handler(void);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_breakpoint_handler(void);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_load_store_fault_handler(void);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_machine_ecall_handler(void);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_user_ecall_handler(void);

OT_WEAK
void ottf_software_isr(void) {
  generic_fault_print("Software IRQ", ibex_mcause_read());
  abort();
}

OT_WEAK
void ottf_timer_isr(void) {
  generic_fault_print("Timer IRQ", ibex_mcause_read());
  abort();
}

OT_WEAK
void ottf_external_isr(void) {
  generic_fault_print("External IRQ", ibex_mcause_read());
  abort();
}

static void generic_internal_irq_handler(void) {
  generic_fault_print("Internal IRQ", ibex_mcause_read());
  abort();
}

OT_WEAK
OT_ALIAS("generic_internal_irq_handler")
void ottf_external_nmi_handler(void);

OT_WEAK
OT_ALIAS("generic_internal_irq_handler")
void ottf_load_integrity_error_handler(void);

OT_WEAK
void ottf_internal_isr(void) {
  uint32_t mcause = ibex_mcause_read();
  switch ((ottf_internal_irq_id_t)(mcause)) {
    case kInternalIrqLoadInteg:
      ottf_load_integrity_error_handler();
      break;
    case kInternalIrqNmi:
      ottf_external_nmi_handler();
      break;
    default:
      generic_internal_irq_handler();
  }
}
