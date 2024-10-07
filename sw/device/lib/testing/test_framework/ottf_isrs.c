// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_isrs.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "devicetables.h"

dif_rv_plic_t ottf_plic;
static const dt_uart_t *kUart0Dt = &kDtUart[0];
static const dt_sram_ctrl_t *kSramCtrlDt = &kDtSramCtrl[1];

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

static const char *exc_frame[] = {
    "mepc", "  ra", "  t0", "  t1", "  t2", "  s0", "  s1", "  a0",
    "  a1", "  a2", "  a3", "  a4", "  a5", "  a6", "  a7", "  s2",
    "  s3", "  s4", "  s5", "  s6", "  s7", "  s8", "  s9", " s10",
    " s11", "  t3", "  t4", "  t5", "  t6", "msts",
};

void ottf_generic_fault_print(uint32_t *exc_info, const char *reason,
                              uint32_t mcause) {
  enum { kExcWords = 30 };
  uint32_t mepc = ibex_mepc_read();
  uint32_t mtval = ibex_mtval_read();
  if (exc_info) {
    base_printf("===== Exception Frame @ %08x =====", exc_info);
    for (size_t i = 0; i < kExcWords; ++i) {
      if (i % 4 == 0) {
        base_printf("\n");
      }
      const char *name = exc_frame[i];
      if (name == NULL)
        continue;
      base_printf(" %4s=%08x", name, exc_info[i]);
    }
    uint32_t *sp = exc_info + kExcWords;
    base_printf("\n");
    uint32_t *ram_start = (uint32_t *)dt_sram_ctrl_reg_block(kSramCtrlDt, kDtSramCtrlRegBlockRam);
    // FIXME figure out how to handle memory sizes without a bunch of ifdefs: maybe add a DT field?
    uint32_t *ram_end =
        (uint32_t *)(dt_sram_ctrl_reg_block(kSramCtrlDt, kDtSramCtrlRegBlockRam) +
                     0x20000);

    extern const char _text_start[], _text_end[];
    const uint32_t text_start = (uint32_t)_text_start;
    const uint32_t text_end = (uint32_t)_text_end;
    base_printf("===== Call Stack =====\n");
    for (; sp >= ram_start && sp < ram_end; ++sp) {
      uint32_t val = *sp;
      if (val >= text_start && val < text_end) {
        base_printf("    %08x\n", val);
      }
    }
  }
  LOG_ERROR("FAULT: %s. MCAUSE=%08x MEPC=%08x MTVAL=%08x", reason, mcause, mepc,
            mtval);
}

static void generic_fault_handler(uint32_t *exc_info) {
  uint32_t mcause = ibex_mcause_read();
  ottf_generic_fault_print(exc_info, exception_reason[mcause & kIbexExcMax],
                           mcause);
  abort();
}

/**
 * The weak `pxCurrentTCB` symbol below enable the OTTF ISRs to be used without
 * the OTTF itself. This enables us to maintain one set of default ISRs for
 * testing, while also enabling writing tests that do not make use of the OTTF.
 * See the `crt_test` in `sw/device/tests/crt_test.c` for an example.
 */
OT_WEAK
void *pxCurrentTCB = NULL;

OT_WEAK
void ottf_exception_handler(uint32_t *exc_info) {
  uint32_t mcause = ibex_mcause_read();

  switch ((ibex_exc_t)(mcause & kIbexExcMax)) {
    case kIbexExcInstrMisaligned:
      ottf_instr_misaligned_fault_handler(exc_info);
      break;
    case kIbexExcInstrAccessFault:
      ottf_instr_access_fault_handler(exc_info);
      break;
    case kIbexExcIllegalInstrFault:
      ottf_illegal_instr_fault_handler(exc_info);
      break;
    case kIbexExcBreakpoint:
      ottf_breakpoint_handler(exc_info);
      break;
    case kIbexExcLoadAccessFault:
      ottf_load_store_fault_handler(exc_info);
      break;
    case kIbexExcStoreAccessFault:
      ottf_load_store_fault_handler(exc_info);
      break;
    case kIbexExcMachineECall:
      ottf_machine_ecall_handler(exc_info);
      break;
    case kIbexExcUserECall:
      ottf_user_ecall_handler(exc_info);
      break;
    default:
      generic_fault_handler(exc_info);
  }
}

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_instr_misaligned_fault_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_instr_access_fault_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_illegal_instr_fault_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_breakpoint_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_load_store_fault_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_machine_ecall_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_fault_handler")
void ottf_user_ecall_handler(uint32_t *exc_info);

OT_WEAK
void ottf_software_isr(uint32_t *exc_info) {
  ottf_generic_fault_print(exc_info, "Software IRQ", ibex_mcause_read());
  abort();
}

OT_WEAK
void ottf_timer_isr(uint32_t *exc_info) {
  ottf_generic_fault_print(exc_info, "Timer IRQ", ibex_mcause_read());
  abort();
}

OT_WEAK
bool ottf_console_flow_control_isr(uint32_t *exc_info) { return false; }

OT_WEAK
void ottf_external_isr(uint32_t *exc_info) {
  const uint32_t kPlicTarget = 0;
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&ottf_plic, kPlicTarget, &plic_irq_id));

  dt_device_id_t peripheral = dt_plic_id_to_device_id(plic_irq_id);

  if (peripheral == dt_uart_device_id(kUart0Dt) &&
      ottf_console_flow_control_isr(exc_info)) {
    // Complete the IRQ at PLIC.
    CHECK_DIF_OK(
        dif_rv_plic_irq_complete(&ottf_plic, kPlicTarget, plic_irq_id));
    return;
  }

  ottf_generic_fault_print(exc_info, "External IRQ", ibex_mcause_read());
  abort();
}

static void generic_internal_irq_handler(uint32_t *exc_info) {
  ottf_generic_fault_print(exc_info, "Internal IRQ", ibex_mcause_read());
  abort();
}

OT_WEAK
OT_ALIAS("generic_internal_irq_handler")
void ottf_external_nmi_handler(uint32_t *exc_info);

OT_WEAK
OT_ALIAS("generic_internal_irq_handler")
void ottf_load_integrity_error_handler(uint32_t *exc_info);

OT_WEAK
void ottf_internal_isr(uint32_t *exc_info) {
  uint32_t mcause = ibex_mcause_read();
  switch ((ibex_internal_irq_t)(mcause)) {
    case kIbexInternalIrqLoadInteg:
      ottf_load_integrity_error_handler(exc_info);
      break;
    case kIbexInternalIrqNmi:
      ottf_external_nmi_handler(exc_info);
      break;
    default:
      generic_internal_irq_handler(exc_info);
  }
}
