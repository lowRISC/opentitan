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


#define L2_BASE_ADDR 0x78000000
#define L3_BASE_ADDR 0x80400000
#define EOC 0xc11c0018
#define NUM_ITER 30
#define L2
#define L3

int main(int argc, char **argv) {

  int * pointer;
  int check_l2 = 0;
  int check_l3 = 0;

#ifdef L2
  // L2 addressability
  for (int i=0; i<NUM_ITER; i++){
    pointer = (int *) L2_BASE_ADDR + i*4;
   *pointer = i*4;
  }

  for (int i=0; i<NUM_ITER; i++){
    pointer = (int *) L2_BASE_ADDR + i*4;
    if(*pointer == i*4)
      check_l2++;
  }
#else
  check_l2 = NUM_ITER;
#endif

#ifdef L3
  // L3 addressability
  for (int i=0; i<NUM_ITER; i++){
    pointer = (int *) L3_BASE_ADDR + i*4;
   *pointer = i*4;
  }
  for (int i=0; i<NUM_ITER; i++){
    pointer = (int *) L3_BASE_ADDR + i*4;
    if(*pointer == i*4)
      check_l3++;
  }
#else
  check_l3 = NUM_ITER;
#endif

  // Checking the results
  if( check_l2 == NUM_ITER && check_l3 == NUM_ITER )
    return 0;
  else
    pointer = (int *) EOC;
   *pointer = 0xffffffff;
    while(1);
}


void external_irq_handler(void)  {
}
