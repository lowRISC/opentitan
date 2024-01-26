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

  int baud_rate = 115200;
  int test_freq = 100000000;
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  int volatile  * ptr;
  int buff;
  for(int i = 0; i<1024; i++){
    ptr = (int *) 0xfff00000 + i*4;
    *ptr = i;
  }
  for(int i = 0; i<1024; i++){
    ptr = (int *) 0xfff00000 + i*4;
    if(*ptr=!i){
      ptr = (int *) 0xc11c0018;
      *ptr = 0xffffffff;
    }
  }
  return 0;
}
