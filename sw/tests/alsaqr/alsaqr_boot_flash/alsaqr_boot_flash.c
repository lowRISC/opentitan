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

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/cfi.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom/boot_policy.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"
#include "sw/device/silicon_creator/rom/rom_epmp.h"
#include "sw/device/silicon_creator/rom/sigverify_keys.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/silicon_creator/lib/rom_print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/base/mmio.h"
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
  pointer = (int *) PLIC_BASE+mbox_id;
  *pointer = 0x1;

  pointer = (int *) 0x0C002090;
  *pointer =  1<<(mbox_id%32);

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
