#include <stdio.h>
#include <stdlib.h>
#include "pulp.h"

#define SHARED_ADDR 0x10000000
#define SIZE 1024

#define L3_BASE 0x80000000
#define L2_BASE 0x1C001000

#define SNOOP_BASE 0x71000000

int main() {

  int error;

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
    error = 0;
    // Write L2, L3, Snooper
    for(int i=0;i<SIZE;i++)
      pulp_write32(L2_BASE + i*0x4, i*0x4);

    for(int i=0;i<SIZE;i++)
      pulp_write32(L3_BASE + i*0x4, i*0x4);

    for(int i=0;i<SIZE;i++)
      pulp_write32(SNOOP_BASE + i*0x4, i*0x4);

    // Return interrupt to Ibex
    pulp_write32(0x10404020, 0x1);
  }

  while (1) {
          __asm__ volatile("wfi;");
  }

  return 0;
}
