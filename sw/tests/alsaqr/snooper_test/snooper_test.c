// Copyright (c) 2022 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
//

#include "sw/tests/common/utils.h"
#include <stdbool.h>

#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/tests/alsaqr/snooper_test/snooper_test.h"

#define SNOOP_BASE    0x10405000
#define AXI_PORT_BASE 0x71000000

#define SNOOP_ID 158
#define PRIO 0x1

#define INSTR
//#define CORE_1

// Function to set a specific bit in the register
void set_register_bit(uint32_t base_addr, uint32_t reg_offset, uint32_t bit_position) {
    uint32_t reg_value = abs_mmio_read32(base_addr + reg_offset);
    reg_value |= (1 << bit_position);
    abs_mmio_write32(base_addr + reg_offset, reg_value);
}

static dif_rv_plic_t plic0;

int main(int argc, char **argv) {

  #ifdef TARGET_SYNTHESIS
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  unsigned val = 0xe0000001;
  bool t;

  int err = 0;
  int base, last;

  asm volatile("csrw mtvec, %0\n" : : "r"(val));

  unsigned val_1 = 0x00001808;  // Set global interrupt enable in ibex regs
  unsigned val_2 = 0x00000800;  // Set external interrupts

  asm volatile("csrw  mstatus, %0\n" : : "r"(val_1));
  asm volatile("csrw  mie, %0\n"     : : "r"(val_2));

  // Init entropy source
  abs_mmio_write32(0xc1170014, 0x9996);

  // Configure plic on snooper's irq
  mmio_region_t plic_base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  t = dif_rv_plic_init(plic_base_addr, &plic0);
  t = dif_rv_plic_irq_set_priority(&plic0, SNOOP_ID, PRIO);
  t = dif_rv_plic_irq_set_enabled(&plic0, SNOOP_ID, 0, kDifToggleEnabled);

  // Configuring Snooper
  abs_mmio_write32(SNOOP_BASE + CFG_REGS_RANGE_0_BASE_H_REG_OFFSET, 0x00000000);
  abs_mmio_write32(SNOOP_BASE + CFG_REGS_RANGE_0_BASE_L_REG_OFFSET, 0x80000000);
  abs_mmio_write32(SNOOP_BASE + CFG_REGS_RANGE_0_LAST_H_REG_OFFSET, 0x00000000);
  abs_mmio_write32(SNOOP_BASE + CFG_REGS_RANGE_0_LAST_L_REG_OFFSET, 0x90000000);
  abs_mmio_write32(SNOOP_BASE + CFG_REGS_TRIG_PC0_H_REG_OFFSET, 0x00000000);
  abs_mmio_write32(SNOOP_BASE + CFG_REGS_TRIG_PC0_L_REG_OFFSET, 0x80001048);

  set_register_bit(SNOOP_BASE, CFG_REGS_CTRL_REG_OFFSET,CFG_REGS_CTRL_TRIG_PC_0_BIT);
  set_register_bit(SNOOP_BASE, CFG_REGS_CTRL_REG_OFFSET,CFG_REGS_CTRL_M_MODE_BIT);

  #ifdef CORE_1
  set_register_bit(SNOOP_BASE, CFG_REGS_CTRL_REG_OFFSET,CFG_REGS_CTRL_CORE_SELECT_BIT);
  #endif

  #ifdef INSTR
  set_register_bit(SNOOP_BASE, CFG_REGS_CTRL_REG_OFFSET,CFG_REGS_CTRL_TRACE_MODE_OFFSET);
  #endif

  // trigger snooper to log traces
  set_register_bit(SNOOP_BASE, CFG_REGS_CTRL_REG_OFFSET,CFG_REGS_CTRL_PC_RANGE_0_BIT);

  // Wait for Trigger Irq
  asm volatile ("wfi");

  base = abs_mmio_read32(SNOOP_BASE + CFG_REGS_BASE_REG_OFFSET);
  last = abs_mmio_read32(SNOOP_BASE + CFG_REGS_LAST_REG_OFFSET);

  #ifndef INSTR
  for(int i=base;i<=last;i=i+20){
    printf("Addr: %X; PC SRC:%X; PC_DST:%X; CTR_TYPE:%X\r\n",
           AXI_PORT_BASE + i,
           abs_mmio_read32(AXI_PORT_BASE + i + 0x00),
           abs_mmio_read32(AXI_PORT_BASE + i + 0x08),
           abs_mmio_read32(AXI_PORT_BASE + i + 0x10)
           );
  }
  #else
  for(int i=base;i<=last;i=i+4){
    printf("Addr: %X; INSTR:%X; \r\n",
           AXI_PORT_BASE + i,
           abs_mmio_read32(AXI_PORT_BASE + i)
           );
  }
  #endif

  return err;
}

void external_irq_handler(void){
  dif_rv_plic_irq_id_t claim_irq;
  (void)dif_rv_plic_irq_claim(&plic0, 0, &claim_irq);
  (void)dif_rv_plic_irq_complete(&plic0, 0, claim_irq);
  return;
}
