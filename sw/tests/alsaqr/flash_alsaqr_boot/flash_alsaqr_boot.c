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

#include <stdbool.h>

#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/rom/string_lib.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {

  sec_mmio_init();
  pinmux_init();

  #ifdef TARGET_SYNTHESIS
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  //set_flls();
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  #define PLIC_BASE     0x0C000000
  #define PLIC_CHECK    PLIC_BASE + 0x201004

  //enable bits for sources 0-31
  #define PLIC_EN_BITS  PLIC_BASE + 0x2090

  int * pointer;
  int mbox_id = 10;

  // Initialazing the uart
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

    // Init CVA6 Plic
  pointer = (int *) 0x0C000028;
  *pointer = 0x1;

  pointer = (int *) 0x0C002080;
  *pointer =  0x400;

  printf("[SECD] Writing CVA6 boot PC into mbox\r\n");
  // Write CVA6 boot PC to mbox
  pointer = (int *) 0x10404000;
  *pointer = 0x80000000;

  printf("[SECD] Booting CVA6\r\n");

  // Send IRQ and boot
  pointer = (int *) 0x10404024;
  *pointer = 0x1;

  while(1)
    asm volatile ("wfi");

  return true;

}
