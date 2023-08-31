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

#include <assert.h>

#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/rom/string_lib.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/silicon_creator/lib/rom_print.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static dif_spi_host_t spi_host;

void init_spi_host(dif_spi_host_t *spi_host,
                   uint32_t peripheral_clock_freq_hz) {
  dif_spi_host_config_t config = {
      .spi_clock = peripheral_clock_freq_hz / 2,
      .peripheral_clock_freq_hz = peripheral_clock_freq_hz,
      .chip_select = {.idle = 2, .trail = 2, .lead = 2},
      .full_cycle = true,
      .cpha = true,
      .cpol = true,
  };
  CHECK_DIF_OK(dif_spi_host_configure(spi_host, config));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, /*enabled=*/true));
}


int main(int argc, char **argv) {
    
  sec_mmio_init();
  pinmux_init();
  uart_init(kUartNCOValue);
  
  volatile int * debug_mode;
  volatile int * address, * start, * payload_1, * payload_2, * payload_3; 
  payload_1  = (int *) 0xff000000;
  payload_2  = (int *) 0xff000004;
  payload_3  = (int *) 0xff000008;
  address    = (int *) 0xff00000C;
  start      = (int *) 0xff000010;
  debug_mode = (int *) 0xff000014;
  
  
  // Setup spi host configuration
  rom_printf("Testing spi_host.\r\n");
  uintptr_t base_addr;
  uint32_t data;
  uint64_t clkHz;
  base_addr = TOP_EARLGREY_SPI_HOST0_BASE_ADDR;
  clkHz = 10000000;
 
  CHECK_DIF_OK(dif_spi_host_init(mmio_region_from_addr(base_addr), &spi_host));
  init_spi_host(&spi_host, (uint32_t)clkHz);
  int num_iter = 156;
  int buf_size = 63;
  uint32_t buf[buf_size];
  dif_spi_host_segment_t segments[3];
  uint32_t addr = 0;
  uint32_t addr_swap = 0;
  int index = 0;
  
  *address = 0;
  for(int j=0;j<num_iter;j++){
     addr = j*sizeof(buf);
     addr_swap = bitfield_byteswap32(addr);
     segments[0] = (dif_spi_host_segment_t) {
                   .type = kDifSpiHostSegmentTypeOpcode,
                   .opcode = 0x13,
     };
     segments[1] = (dif_spi_host_segment_t) {
                   .type = kDifSpiHostSegmentTypeAddress,
                   .address =
                      {
                          .width = kDifSpiHostWidthStandard,
                          .mode = kDifSpiHostAddrMode4b,
                          .address = addr_swap,
                      },
     }; 
     segments[2] = (dif_spi_host_segment_t) {
                   .type = kDifSpiHostSegmentTypeRx,
                   .rx =
                      {
                          .width = kDifSpiHostWidthStandard,
                          .buf = buf,
                          .length= sizeof(buf),
                      },
     };

     CHECK_DIF_OK(
          dif_spi_host_transaction(&spi_host, 0, segments, ARRAYSIZE(segments)));
     
     for(int i = 0; i < buf_size; i += 3) {
       if(i + 2 < buf_size) {
         *payload_1 = buf[i];
         *payload_2 = buf[i+1];
         *payload_3 = buf[i+2];
	 *address   = index;
         *start = 0x1;
	 index++;
       }
     }
  } 

  CHECK_DIF_OK(dif_spi_host_output_set_enabled(&spi_host, false));  
  return 0;
}
