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
#define IBEX
#define MBOX
#define ARIANE

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
  
  printf("Writing the crypto key to the HMAC\r\n");
  t = hmac_write_key();  // dummy key
  t = hmac_init();       // write the control register

  printf("Preloading MBOX, Ibex SRAM, Ariane SRAM, HyperRam\r\n");
  t = preload_mbox();
  t = preload_ariane();
  t = preload_ibex();
  t = preload_hyper();
   
  printf("Moving data from Mbox to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_mbox();

  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();

  printf("Moving data from Ariane SRAM to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_ariane();
  
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();
  
  printf("Moving data from Ibex SRAM to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_ibex();

  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();

  printf("Moving data from HyperRAM to HMAC\r\n");
  t = hmac_init(); 
  t = hmac_input_hyper();
  
  printf("Encrypt!\r\n");
  t = hmac_encrypt();
  t = hmac_read_out();

  printf("Test succeed\r\n");

  return 0;
}
