// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_isrs.h"

#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/error.h"

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);

  // TODO(opentitan#22947): Remove this debug print prior to a formal release.
  uint32_t mepc, mtval;
  CSR_READ(CSR_REG_MEPC, &mepc);
  CSR_READ(CSR_REG_MTVAL, &mtval);
  dbg_printf("MCAUSE=%x MEPC=%x MTVAL=%x\r\n", mcause, mepc, mtval);

  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorRomExtInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorRomExtInterrupt + mcause;
}

OT_USED
void rom_ext_interrupt_handler(void) {
#ifdef OT_COVERAGE_INSTRUMENTED
  // Fix gp first in case it's modified by later boot stages.
  asm volatile(
      ".option push\n"
      ".option norelax\n"
      "la gp, __global_pointer$\n"
      ".option pop\n");
#endif

  register rom_error_t error asm("a0") = rom_ext_irq_error();
  asm volatile("tail shutdown_finalize;" ::"r"(error));
  OT_UNREACHABLE();
}

// We only need a single handler for all ROM_EXT interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the ROM_EXT,
// alias all interrupt handler symbols to the single handler.
OT_USED
OT_ALIAS("rom_ext_interrupt_handler")
void rom_ext_exception_handler(void);

OT_USED
OT_ALIAS("rom_ext_interrupt_handler")
void rom_ext_nmi_handler(void);
