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
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/test_framework/check.h"

#define MBOX_ID 159
#define PRIO 0x1

static dif_rv_plic_t plic0;

int main(int argc, char **argv) {

  #ifdef TARGET_SYNTHESIS
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  //set_flls();
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  int volatile  * plic_prio, * plic_en;
  int volatile * edn_enable;
  int volatile * p_reg, * p_reg1, * plic_check, * p_reg2, * p_reg3, * p_reg4, * p_reg5 ;
  int a, b, c, e, d;
  bool t;

  unsigned val = 0xe0000001;
  asm volatile("csrw mtvec, %0\n" : : "r"(val));

  unsigned val_1 = 0x00001808;  // Set global interrupt enable in ibex regs
  unsigned val_2 = 0x00000800;  // Set external interrupts

  asm volatile("csrw  mstatus, %0\n" : : "r"(val_1));
  asm volatile("csrw  mie, %0\n"     : : "r"(val_2));

  edn_enable = (int *) 0xc1170014;
 *edn_enable = 0x9996;

  printf("FPGA test with two indipendent JTAG for Ibex and Ariane\r\n");
  mmio_region_t plic_base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  t = dif_rv_plic_init(plic_base_addr, &plic0);
  t = dif_rv_plic_irq_set_priority(&plic0, MBOX_ID, PRIO);
  t = dif_rv_plic_irq_set_enabled(&plic0, MBOX_ID, 0, kDifToggleEnabled);

  printf("Ibex: Writing and reading the mailbox\r\n");
  uart_wait_tx_done();
  p_reg = (int *) 0x10404000;
 *p_reg = 0xbaadc0de;

  a = *p_reg;

  if(a == 0xbaadc0de){
     printf("Ibex: R & W succeeded\r\nIbex: Going in wfi\r\n");
     uart_wait_tx_done();
  }
  else{
     printf("Test failed, the mbox has not been accessed correctly\r\n");
     uart_wait_tx_done();
  }

  asm volatile ("wfi"); // Ready to receive a command from the Agent --> Jump to the External_Irq_Handler
//init pointer to check memory

  p_reg1 = (int *) 0x10404008;
  p_reg2 = (int *) 0x10404010;
  p_reg3 = (int *) 0x10404014;
  p_reg4 = (int *) 0x10404018;
  p_reg5 = (int *) 0x1040401C;

  a = *p_reg1;
  b = *p_reg2;
  c = *p_reg3;
  d = *p_reg4;
  e = *p_reg5;

  if( a == 0xBAADC0DE &&  b == 0xBAADC0DE && c == 0xBAADC0DE && d == 0xBAADC0DE && e == 0xBAADC0DE){
     p_reg = (int *) 0x10404024; // completion interrupt to ariane agent
    *p_reg = 0x00000001;
    printf("Raising back irq to ariane\r\n");
    while(1);
  }
  else
    printf("Error\r\n");
  return 0;
}

void external_irq_handler(void){
  volatile int * p_reg;
  //clearing the pending interrupt signal
  p_reg = (int *) 0x10404020;
 *p_reg = 0x00000000;
  dif_rv_plic_irq_id_t claim_irq;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic0, 0, &claim_irq));
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic0, 0, claim_irq));
  return;
}
