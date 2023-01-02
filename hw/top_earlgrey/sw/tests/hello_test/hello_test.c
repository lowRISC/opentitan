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

#include "simple_system_common.h"
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
  
  int volatile  * plic_prio, * plic_en;
  int volatile * p_reg, * p_reg1;
  int a = 0;
 
  unsigned val = 0xe0000001;
  asm volatile("csrw mtvec, %0\n" : : "r"(val));
  

  printf("FPGA test with two indipendent JTAG for Ibex and Ariane\r\n");
  uart_wait_tx_done();
  unsigned val_1 = 0x00001808;  // Set global interrupt enable in ibex regs
  unsigned val_2 = 0x00000800;  // Set external interrupts

  asm volatile("csrw  mstatus, %0\n" : : "r"(val_1)); 
  asm volatile("csrw  mie, %0\n"     : : "r"(val_2));

  plic_prio  = (int *) 0xC8000110;  // Priority reg
  plic_en    = (int *) 0xC8002008;  // Enable reg

 *plic_prio  = 1;                   // Set mbox interrupt priority to 1
 *plic_en    = 0x00000010;          // Enable interrupt
 
  printf("Ibex: Writing and reading to the mailbox\r\n");
  uart_wait_tx_done();
  p_reg = (int *) 0x10404000;
 *p_reg = 0xbaadc0de;

  a = *p_reg;
  
  if(a == 0xbaadc0de){
     printf("Ibex: R & W succeeded\r\nGoing in wfi\r\n");
     uart_wait_tx_done();
  }
  else{
     printf("Test failed, the mbox has not been accessed correctly\r\n");
     uart_wait_tx_done();
  }
  /////////////////////////// Wait for shared memory test to start ///////////////////////////////
  
  
  while(1)
    asm volatile ("wfi"); // Ready to receive a command from the Agent --> Jump to the External_Irq_Handler

  return 0;
  
}
