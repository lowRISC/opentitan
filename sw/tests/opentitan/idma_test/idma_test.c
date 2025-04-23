#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"

#define IDMA_BASE 		 0xfef00000
#define TCDM_BASE      0xfff00000
#define L2_BASE        0x1C001000
#define L3_BASE        0x80000000

#define SIZE           0x1000 //4KiB

#define IDMA_SRC_ADDR_OFFSET         0x000000d8
#define IDMA_DST_ADDR_OFFSET         0x000000d0
#define IDMA_LENGTH_OFFSET           0x000000e0
#define IDMA_NEXT_ID_OFFSET          0x00000044
#define IDMA_DONE_ID_OFFSET          0x00000084
#define IDMA_REPS_2                  0x000000f8
#define IDMA_REPS_3                  0x00000110
#define IDMA_CONF                    0x00000000
#define EOC                          0xc11c0018

void wait_for_idma_eot(int next_id){
    volatile uint32_t *ptr;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_DONE_ID_OFFSET) ;
    while(*ptr!=next_id)
      asm volatile("nop");
}

int issue_idma_transaction(uint32_t src_addr, uint32_t dst_addr, uint32_t num_bytes){
    volatile uint32_t * ptr;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_SRC_ADDR_OFFSET);
    *ptr = src_addr;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_DST_ADDR_OFFSET);
    *ptr = dst_addr;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_LENGTH_OFFSET);
    *ptr = num_bytes;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_CONF);
    *ptr = 0x3<<10;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_REPS_2);
    *ptr = 0x00000001;
    ptr = (uint32_t *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
    return *ptr;
}

int main() {

  int volatile  * ptr;
  int b;
  int err = 0;

  int next_id;

  for(int i = 0; i<1024; i++){
    ptr = (int *) TCDM_BASE + i*4;
    *ptr = i;
  }

  next_id = issue_idma_transaction(TCDM_BASE,L2_BASE,SIZE);

  wait_for_idma_eot(next_id);

  for(int i = 0; i<SIZE/4; i++){
    ptr = (int *) L2_BASE + i;
    b = *ptr;
    if(b!=i)
      err++;
  }

  if(err!=0){
    ptr = (int *) EOC;
    *ptr = 0xFFFFFFFF;
    return -1;
  }
  else
    return 0;

}
