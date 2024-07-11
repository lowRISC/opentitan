#include <stdio.h>
#include <stdlib.h>
#include "pulp.h"

#define SHARED_ADDR 0x10000000

int main() {

  if(core_id() == 0) {
    pulp_write32(SHARED_ADDR, 0);
    pulp_write32(SHARED_ADDR, pulp_read32(SHARED_ADDR) + 1);
  }

  synch_barrier();

  while(pulp_read32(SHARED_ADDR) < core_id());

  if(core_id() != 0) {
  pulp_write32(SHARED_ADDR,pulp_read32(SHARED_ADDR)+1);
  }

  synch_barrier();

  if(core_id() == 0){
    pulp_write32(0x10404008, 0xBAADC0DE);
    pulp_write32(0x10404010, 0xBAADC0DE);
    pulp_write32(0x10404014, 0xBAADC0DE);
    pulp_write32(0x10404018, 0xBAADC0DE);
    pulp_write32(0x1040401C, 0xBAADC0DE);
    pulp_write32(0x10404020, 0x1); //ring doorbell
  }

  while (1) {
          __asm__ volatile("wfi;");
  }

  return 0;
}
