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
#include "../hmac_smoketest/hmac_smoketest_clear32.h"

#include "../common/utils.h"
#include <stdbool.h>

#define TARGET_SYNTHESIS

int main(int argc, char **argv) {

  volatile int * debug_mode;
  volatile int * flash_addr;

  int errors = 0;
  int i = 0;
  int exp,read;
  
  flash_addr = (int *) 0xf0000000;
  debug_mode = (int *) 0xff000014;

  #ifdef TARGET_SYNTHESIS                
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  //set_flls();
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);


  for(i = 0; i < buffer_size_clear; i=i+2){
    flash_addr = (int *)(0xf0000000 + i*0x4);
    read = *flash_addr;
    exp = HMAC_SMOKETEST_CLEAR[i+1];
    if(read==exp)
      printf("Correct! Addr: %x, Exptected Data: %x, Read Data: %x\r\n",flash_addr,exp, read);
    else{
      printf("Error! Addr: %x, Exptected Data: %x, Read Data: %x\r\n",flash_addr,exp, read);
      errors++;
    }
    flash_addr = (int *)(0xf0000000 + (i+1)*0x4);
    read = *flash_addr;
    exp = HMAC_SMOKETEST_CLEAR[i];
    if(read==exp)
      printf("Correct! Addr: %x, Exptected Data: %x, Read Data: %x\r\n",flash_addr,exp,read);
    else{
      printf("Error! Addr: %x, Exptected Data: %x, Read Data: %x\r\n",flash_addr,exp, read);
      errors++;
    }
    flash_addr = (int *)(0xf0000000 + (i+2)*0x4);
  }

  printf("Total Correct: %x/%x", (i-errors), i);
  printf("Total Errors: %x/%x", errors, i);
  *debug_mode = 0x0;
  
  return 0;
  
}
