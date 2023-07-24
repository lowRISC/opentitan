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

#define S_0  0x03000000
#define S_1  0x03000004
#define S_2  0x03000008
#define LLC  0x03001000

int main(int argc, char **argv) {

  int * pointer;
  /*pointer = (int *) LLC;
  while(!*pointer);
  */
  pointer = (int *) S_1;
  *pointer = 0x00000000;
  
  pointer = (int *) S_0;
  *pointer = 0x78000000;

  pointer = (int *) S_2;
  *pointer = 2;  
  
  while(1)
    asm volatile ("wfi"); 

  return 0;
  
}


void external_irq_handler(void)  {
}
