// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
///***

#include "sw/device/lib/base/abs_mmio.h"
#include "csrng_regs.h"  // Generated

///***
#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/silicon_creator/rom/uart.h"
#include "sw/device/silicon_creator/rom/string_lib.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define TIMEOUT (1000 * 1000)
#define BASE_PERFCOUNTERS_T  0x00020000



int main(int argc, char **argv) {
  uint32_t rd_val;
  #ifdef TARGET_SYNTHESIS
  int baud_rate = 115200;
  int test_freq = 50000000;
  #else
  //set_flls();
  int baud_rate = 115200;
  int test_freq = 100000000;
  #endif
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

/*
 *
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_REG_OFFSET = 6'h 0;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENTS_COUNTERS_MUX_REG_OFFSET = 6'h 4;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_COUNTERS_RST_REG_OFFSET = 6'h 8;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_COUNTER3_REG_OFFSET = 6'h C;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_COUNTER2_REG_OFFSET = 6'h 10;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_COUNTER1_REG_OFFSET = 6'h 14;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_COUNTER0_REG_OFFSET = 6'h 18;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_CLK_COUNTER3_REG_OFFSET = 6'h 1C;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_CLK_COUNTER2_REG_OFFSET = 6'h 20;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_CLK_COUNTER1_REG_OFFSET = 6'h 24;
  parameter logic [BlockAw-1:0] PERFCOUNTERS_T_EVENT_CLK_COUNTER0_REG_OFFSET = 6'h 28;
*/
  printf("EVENT1 to COUNTER2 EVENT2 to COUNTER0 MUX\r\n");
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x4, 0x42);

  printf("EVENT 2 to write 256 \r\n");
  for (int i=0;i<256;i++) {
  	abs_mmio_write32(BASE_PERFCOUNTERS_T+0x0, 0x4);
  }
  printf("EVENT COUNTERS RESET  \r\n");
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x8, 0xFF);
  
  printf("EVENT 2 to write 331 \r\n");
  for (int i=0;i<331;i++) {
  	abs_mmio_write32(BASE_PERFCOUNTERS_T+0x0, 0x4);
  }
 
  printf("EVENT 1 to write \r\n");
  for (int i=0;i<35;i++) {
  	abs_mmio_write32(BASE_PERFCOUNTERS_T+0x0, 0x2);
  }

  printf("EVENT 2 to READ \r\n");
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0xC);
  printf("EVENT COUNTER3_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x10);
  printf("EVENT COUNTER2_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x14);
  printf("EVENT COUNTER1_REG READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x18);
  printf("EVENT COUNTER0_REG READ %x  \r\n",rd_val);

  // *** EVENT CLK COUNTERS ****
  //

  printf("EVENT CLK COUNTER3-2 RESET  \r\n");
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x8, 0xA0);

  printf("EVENT CLK COUNTERS  READ \r\n");
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x1C);
  printf("EVENT CLK_COUNTER3_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x20);
  printf("EVENT CLK_COUNTER2_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x24);
  printf("EVENT CLK_COUNTER1_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x28);
  printf("EVENT CLK_COUNTER0_REG  READ %x  \r\n",rd_val);


    // *** EVENT COUNTERS ****
  printf("EVENT7 to COUNTER3 EVENT3 to COUNTER2 MUX \r\n");
  // 111 011 000 000
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x4, 0xEC0);

  printf("EVENT 7 to write \r\n");
  for (int i=0;i<256;i++) {
        abs_mmio_write32(BASE_PERFCOUNTERS_T+0x0, 0x80);
  }
  printf("EVENT COUNTERS RESET  \r\n");
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x8, 0xFF);

  printf("EVENT 7 to write 332 \r\n");
  for (int i=0;i<331;i++) {
        abs_mmio_write32(BASE_PERFCOUNTERS_T+0x0, 0x80);
  }

  printf("EVENT 3 to write \r\n");
  for (int i=0;i<50;i++) {
        abs_mmio_write32(BASE_PERFCOUNTERS_T+0x0, 0x8);
  }

  printf("EVENT 2 to READ \r\n");
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0xC);
  printf("EVENT COUNTER3_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x10);
  printf("EVENT COUNTER2_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x14);
  printf("EVENT COUNTER1_REG READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x18);
  printf("EVENT COUNTER0_REG READ %x  \r\n",rd_val);




  // *** EVENT CLK COUNTERS ****
  //
  printf("EVENT CLK COUNTER2- RESET  \r\n");
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x8, 0x20);
  printf("EVENT CLK COUNTERS  READ \r\n");

  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x1C);
  printf("EVENT CLK_COUNTER3_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x20);
  printf("EVENT CLK_COUNTER2_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x24);
  printf("EVENT CLK_COUNTER1_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x28);
  printf("EVENT CLK_COUNTER0_REG  READ %x  \r\n",rd_val);


  printf("EVENT CLK COUNTER0- RESET  \r\n");
  abs_mmio_write32(BASE_PERFCOUNTERS_T+0x8, 0x02);
  printf("EVENT CLK COUNTERS  READ \r\n");

  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x1C);
  printf("EVENT CLK_COUNTER3_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x20);
  printf("EVENT CLK_COUNTER2_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x24);
  printf("EVENT CLK_COUNTER1_REG  READ %x  \r\n",rd_val);
  rd_val = abs_mmio_read32(BASE_PERFCOUNTERS_T+0x28);
  printf("EVENT CLK_COUNTER0_REG  READ %x  \r\n",rd_val);

  printf("Succeed!\r\n");
  return 1;
}
