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
#include "../flash_hmac_smoketest/bazel-out/flash_hmac_smoketest_signed32.h"

#include "../common/utils.h"
#include <stdbool.h>

#define TARGET_SYNTHESIS

int main(int argc, char **argv) {

  volatile int * datapath, * sw_bootmode;
  volatile int * payload_1, * payload_2, * payload_3, * address, * start;

  int errors = 0;
  int i = 0;
  
  payload_1   = (int *) 0xff000000;
  payload_2   = (int *) 0xff000004;
  payload_3   = (int *) 0xff000008;
  address     = (int *) 0xff00000C;
  start       = (int *) 0xff000010;
  sw_bootmode = (int *) 0xff000018;
  datapath    = (int *) 0xff00001C;

  *datapath = 0x1;
  
  for(int i = 0; i < buffer_size; i += 3) {
     if(i + 2 < buffer_size) {
        *payload_1 = FLASH_HMAC_SMOKETEST_SIGNED[i];
        *payload_2 = FLASH_HMAC_SMOKETEST_SIGNED[i+1];
        *payload_3 = FLASH_HMAC_SMOKETEST_SIGNED[i+2];
        *address = i/3;
        *start = 0x1;
     }
  }

  *datapath = 0x0;
  *sw_bootmode = 0x1;
  
  return 0;
  
}
