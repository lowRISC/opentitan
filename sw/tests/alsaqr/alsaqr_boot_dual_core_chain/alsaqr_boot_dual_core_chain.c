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

#include "utils.h"
#include <stdbool.h>

#define TARGET_SYNTHESIS

int main(int argc, char **argv) {


  #ifdef TARGET_SYNTHESIS
  int baud_rate = 115200;
  int test_freq = 40000000;
  #else
  //set_flls();
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  int * pointer;

  int volatile  * plic_prio, * plic_en;

  int mbox_id = 10;

  unsigned val_1 = 0x00001808;  // Set global interrupt enable in ibex regs
  unsigned val_2 = 0x00000800;  // Set external interrupts

  unsigned val = 0xe0000001;
  asm volatile("csrw mtvec, %0\n" : : "r"(val));
  asm volatile("csrw  mstatus, %0\n" : : "r"(val_1));
  asm volatile("csrw  mie, %0\n"     : : "r"(val_2));

  plic_prio  = (int *) 0xC800027C;  // Priority reg
  plic_en    = (int *) 0xC8002010;  // Enable reg

 *plic_prio  = 1;                   // Set mbox interrupt priority to 1
 *plic_en    = 0x80000000;          // Enable interrupt

  // Initialazing the uart
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  // Set plic mbox irq prio
  pointer = (int *) 0x0C000028;
  *pointer = 0x1;

  // Enable mbox irq to Core 0
  pointer = (int *) 0x0C002080;
  *pointer =  0x400;
  // Write CVA6 boot PC to mbox
  pointer = (int *) 0x10404000;
  *pointer = 0x80000000;
  // Send IRQ to boot core 0
  pointer = (int *) 0x10404024;
  *pointer = 0x1;

  // wait for completion of irq
  asm volatile ("wfi");


  // Disable mbox irq to Core 1
  pointer = (int *) 0x0C002080;
  *pointer = 0x0;
  // un-set plic mbox irq prio
  pointer = (int *) 0x0C000028;
  *pointer = 0x0;

  printf("[SECD] Booted CVA6 core 0, going wfi\r\n");
  uart_wait_tx_done();

  while(1)
    asm volatile ("wfi");

  return 0;

}

void external_irq_handler(void) {
  int * pointer;
  int mbox_id = 159;
  pointer = (int *) 0xC8200004;
  while(*pointer!=mbox_id)
  *pointer = mbox_id;
  pointer = (int *) 0x10404020;
  *pointer = 0x0;
}
