#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"
#include "cluster_code.h"

int main() {

  //////////////////////////////
  // PLIC UART and IRQ config //
  //////////////////////////////

  #ifdef TARGET_SYNTHESIS
  int baud_rate = 115200;
  int test_freq = 40000000;
  #else
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg_cl(0,(test_freq/baud_rate)>>4);

  volatile int * fetch_en, * edn_enable, * plic_prio, * plic_en;
  volatile int * p_reg;

  p_reg = (int *) 0x10404008;

  int a, b, c, e, d, err;

  fetch_en = (int *) 0xff000020;

  unsigned val = 0xe0000001;
  asm volatile("csrw mtvec, %0\n" : : "r"(val));

  unsigned val_1 = 0x00001808;  // Set global interrupt enable in ibex regs
  unsigned val_2 = 0x00000800;  // Set external interrupts

  asm volatile("csrw  mstatus, %0\n" : : "r"(val_1));
  asm volatile("csrw  mie, %0\n"     : : "r"(val_2));

  plic_prio  = (int *) 0xC800027C;  // Priority reg
  plic_en    = (int *) 0xC8002010;  // Enable reg

 *plic_prio  = 1;                   // Set mbox interrupt priority to 1
 *plic_en    = 0x80000000;          // Enable interrupt

  edn_enable = (int *) 0xc1170014;
  *edn_enable = 0x9996;

  /////////////////////////
  // Cluster offloading  //
  /////////////////////////

  err = load_cluster_code();
  if(err==0) printf_cl("Cluster preloaded, now wfi!\r\n");

  *fetch_en = 0x1;

  asm volatile ("wfi");
  
  if(*p_reg != 0){
    printf_cl("Matmul wrong result!\r\n");
    return -1;
  }

  printf_cl("Cluster raised irq to Ibex, test succeed!\r\n");
  return 0;
}

void external_irq_handler(void){
  int mbox_id = 159;
  int volatile * p_reg, * plic_check;

  // start of """Interrupt Service Routine"""

  plic_check = (int *) 0xC8200004;
  while(*plic_check != mbox_id);   //check wether the intr is the correct one

  p_reg = (int *) 0x10404020;
 *p_reg = 0x00000000;        //clearing the pending interrupt signal

 *plic_check = mbox_id;      //completing interrupt

  return;
}
