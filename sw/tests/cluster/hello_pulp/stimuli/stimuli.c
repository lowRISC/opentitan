#include <stdio.h>
#include <stdlib.h>
#include "pulp.h"
// #define FPGA_EMULATION

#ifdef FPGA_EMULATION
  int baud_rate = 115200;
  int test_freq = 50000000;
#else
  int baud_rate = 115200;
  int test_freq = 100000000;
#endif

#define SHARED_ADDR 0x10000000

//int main(int argc, char const *argv[]) {
int main() {

  if(core_id() == 0) {

    pulp_write32(SHARED_ADDR, 0);

    #ifdef USE_UART
    uart_set_cfg(0, (test_freq / baud_rate) >> 4);
    printf("UART BASE: %X\n", UART_BASE_ADDR);
    printf("%d\n", core_id());
    uart_wait_tx_done();
    #endif

    pulp_write32(SHARED_ADDR, pulp_read32(SHARED_ADDR) + 1);
  }

  synch_barrier();

  while(pulp_read32(SHARED_ADDR) < core_id());

  if(core_id() != 0) {

  #ifdef USE_UART
  printf("%d\n",core_id());
  uart_wait_tx_done();
  #endif

  pulp_write32(SHARED_ADDR,pulp_read32(SHARED_ADDR)+1);
  }

  synch_barrier();

  if(core_id() == 0){
    // Write msg to mailbox
    pulp_write32(0x10403000 + 0x00, 0);
  }

  while (1) {
          __asm__ volatile("wfi;");
  }

  return 0;
}
