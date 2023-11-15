// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdalign.h>

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "uart_regs.h"  // Generated.

dif_rv_plic_t plic;

void fault_test_main(void) {
#if defined(LOAD_ACCESS_FAULT)
  // This address is not a valid address.  It is located near the end of the
  // peripheral MMIO regiion 0x4000_0000 to 0x5000_0000, but there is no
  // peripheral located there.
  //
  // We expeect the ROM_EXT to report BFV:05524902.
  volatile uint32_t *p = (volatile uint32_t *)0x4FFF0000;
  uint32_t value = *p;
  dbg_printf("Got value: %x\r\n", value);
  dbg_printf("LOAD_ACCESS_FAULT: FAIL!\r\n");
#elif defined(STORE_ACCESS_FAULT)
  // This address is not a valid address.  It is located near the end of the
  // peripheral MMIO regiion 0x4000_0000 to 0x5000_0000, but there is no
  // peripheral located there.
  //
  // We expeect the ROM_EXT to report BFV:07524902.
  volatile uint32_t *p = (volatile uint32_t *)0x4FFF0000;
  *p = 100;
  dbg_printf("STORE_ACCESS_FAULT: FAIL!\r\n");
#elif defined(ILLEGAL_INSTRUCTION_FAULT)
  // The "HARDENED_TRAP" emits some "unimp" instructions into the instruction
  // stream.
  //
  // We expeect the ROM_EXT to report BFV:02524902.
  HARDENED_TRAP();
  dbg_printf("ILLEGAL_INSTRUCTION_FAULT: FAIL!\r\n");
#elif defined(HARDWARE_INTERRUPT)
  // To check that hardware interrupts cause a fault, we need to enable
  // IRQs at the CPU, the PLIC and the peripheral itself.  We'll use the
  // UART INTR_TEST register to cause a TX_WATERMARK interrupt.
  //
  // We expeect the ROM_EXT to report BFV:8b524902.
  dif_result_t result = dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic);
  dbg_printf("plic_init = 0x%x\r\n", result);
  // Set IRQ priorities to MAX
  result = (dif_rv_plic_irq_set_priority(
      &plic, kTopEarlgreyPlicIrqIdUart0TxWatermark, kDifRvPlicMaxPriority));
  dbg_printf("plic_set_priority = 0x%x\r\n", result);
  // Set Ibex IRQ priority threshold level
  result = (dif_rv_plic_target_set_threshold(&plic, kTopEarlgreyPlicTargetIbex0,
                                             kDifRvPlicMinPriority));
  dbg_printf("plic_target_set_threshold = 0x%x\r\n", result);
  // Enable IRQs in PLIC
  result = dif_rv_plic_irq_set_enabled(
      &plic, kTopEarlgreyPlicIrqIdUart0TxWatermark, kTopEarlgreyPlicTargetIbex0,
      kDifToggleEnabled);
  dbg_printf("plic_set_enabled = 0x%x\r\n", result);
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  uint32_t val =
      bitfield_bit32_write(0, UART_INTR_COMMON_TX_WATERMARK_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET,
                   val);
  abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_TEST_REG_OFFSET,
                   val);
  dbg_printf("HARDWARE_INTERRUPT: FAIL!\r\n");
#elif defined(NO_FAULT)
  dbg_printf("NO_FAULT: PASS!\r\n");
#else
  dbg_printf("Fault not defined. FAIL!\r\n");
#endif
  while (true) {
  }
}
