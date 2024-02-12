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

int main(int argc, char **argv) {

  int volatile * plic_prio, * plic_en;
  int volatile * p_reg;
  int a = 0;

  unsigned val = 0xe0000001;
  asm volatile("csrw mtvec, %0\n" : : "r"(val)); // move irq vector to SRAM base address

  unsigned val_1 = 0x00001808;      // Set global interrupt enable in ibex regs
  unsigned val_2 = 0x00000800;      // Set external interrupts

  asm volatile("csrw  mstatus, %0\n" : : "r"(val_1));
  asm volatile("csrw  mie, %0\n"     : : "r"(val_2));

  plic_prio  = (int *) 0xC800027C;  // Priority reg
  plic_en    = (int *) 0xC8002010;  // Enable reg

 *plic_prio  = 1;                   // Set mbox interrupt priority to 1
 *plic_en    = 0x80000000;          // Enable interrupt

  while(1)
    asm volatile ("wfi"); // Ready to receive a command from the Agent --> Jump to the External_Irq_Handler

  return 0;

}

void external_irq_handler(void)  {

  int mbox_id = 159;
  int a, b, c, e, d;
  int volatile * p_reg, * p_reg1, * plic_check, * p_reg2, * p_reg3, * p_reg4, * p_reg5 ;

  //init pointer to check memory

  p_reg1 = (int *) 0x40000880;

  // start of """Interrupt Service Routine"""

  plic_check = (int *) 0xC8200004;
  while(*plic_check != mbox_id);   //check wether the intr is the correct one

  p_reg = (int *) 0x40000804;
 *p_reg = 0x00000000;              //clearing the pending interrupt signal

  p_reg = (int *) 0x4000080C;
 *p_reg = 0x00000000;              // disable irq

  p_reg = (int *) 0x40000808;
 *p_reg = 0x00000001;              // raise irq completion (mbox side)

 *plic_check = mbox_id;            // completing interrupt (plic side)

  // check mbox content
  a = *p_reg1;

  if( a == 0xBAADC0DE){
      p_reg = (int *) 0x40000C0C; // completion interrupt to ariane agent if msg = expected msg
     *p_reg = 0x00000001;
      p_reg = (int *) 0x40000C04; // completion interrupt to ariane agent if msg = expected msg
     *p_reg = 0x00000001;
  }
  return;
}
