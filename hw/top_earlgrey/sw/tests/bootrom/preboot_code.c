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

#include "hw/top_earlgrey/sw/tests/common/utils.h"
#include "/sw/device/tests/hmac_smoketest.c"
#include <stdbool.h>

#define TARGET_SYNTHESIS

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
  printf("hello bocola\r\n");
  bool t;
  t = test_main();
  while(1)
    asm volatile ("wfi");

  return 0;
  
}
