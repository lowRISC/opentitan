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

#include "../common/simple_system_common.h"
#include <stdbool.h>
#include "hmac_api.c"

#define HYPER


int main(int argc, char **argv) {

  bool t;

  // UART setup
  #ifdef TARGET_SYNTHESIS                
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);
  
  // move interrupt vector to SRAM base address
  unsigned val = 0xe0000001;                      
  asm volatile("csrw mtvec, %0\n" : : "r"(val));

  printf("Initializing entropy src and HMAC\r\n");
  
  t = entropy_init();    // init the entropy source
  t = hmac_write_key();  // dummy key
  t = hmac_init();       // write the control register
  
  printf("Writing the crypto key to the HMAC\r\n");
  
  

  #ifdef MBOX
  printf("Preloaing the Mbox\r\n");
  t = preload_mbox();
  printf("Moving data from Mbox to HMAC\r\n");
  t = hmac_input_mbox();
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  #endif

  #ifdef ARIANE
  printf("Preloaing the Ariane SRAM\r\n");
  t = preload_ariane();
  printf("Moving data from Ariane SRAM to HMAC\r\n");
  t = hmac_input_ariane();
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  #endif

  #ifdef IBEX
  printf("Preloaing the Ibex SRAM\r\n");
  t = preload_ibex();
  printf("Moving data from Ibex SRAM to HMAC\r\n");
  t = hmac_input_ibex();
  printf("Encrypt!\n\r");
  t = hmac_encrypt();
  #endif

  #ifdef HYPER
  printf("Preloaing the HyperRAM\r\n");
  t = preload_hyper();
  printf("Moving data from HyperRAM to HMAC\r\n");
  t = hmac_input_hyper();
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  #endif

  printf("Test succeed\r\n");

  return 0;
}
