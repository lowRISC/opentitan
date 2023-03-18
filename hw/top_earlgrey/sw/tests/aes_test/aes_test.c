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

#include "../common/utils.h"
#include <stdbool.h>
#include "aes_api.c"

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
  
  printf("Preloading MBOX, Ibex SRAM, Ariane SRAM, HyperRam\r\n");
  t = preload_mbox();
  t = preload_ariane();
  t = preload_ibex();
  t = preload_hyper();
  
  printf("Initializing entropy src and AES\r\n");
  t = entropy_init();   // init the entropy source
  t = aes_init();       // write the control register
  
  printf("Writing the crypto key to the AES\r\n");
  t = aes_write_key();  // dummy key

  printf("Moving data from Mbox to AES\r\n");
  t = aes_input_mbox();
  printf("Encrypt!\r\n");
  t = aes_encrypt();
  t = aes_read_out();

  printf("Moving data from Ariane SRAM to AES\r\n");
  t = aes_input_ariane();
  printf("Encrypt!\r\n");
  t = aes_encrypt();
  t = aes_read_out();
  
  printf("Moving data from Ibex SRAM to AES\r\n");
  t = aes_input_ibex();
  printf("Encrypt!\n\r");
  t = aes_encrypt();
  t = aes_read_out();

  printf("Moving data from HyperRAM to AES\r\n");
  t = aes_input_hyper();
  printf("Encrypt!\r\n");
  t = aes_encrypt();
  t = aes_read_out();
  
  printf("Test succeed\r\n");

  return 0;
}
