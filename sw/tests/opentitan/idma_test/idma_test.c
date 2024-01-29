#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"

#define IDMA_BASE 		 0xfef00000
#define TCDM_BASE      0xfff00000
#define L2_BASE        0x1C001000
#define L3_BASE        0x80000000

#define IDMA_SRC_ADDR_OFFSET         0xd8
#define IDMA_DST_ADDR_OFFSET         0xd0
#define IDMA_LENGTH_OFFSET           0xe0
#define IDMA_NEXT_ID_OFFSET          0x44
#define IDMA_REPS_2_OFFSET           0xf8
int main() {

  int baud_rate = 115200;
  int test_freq = 100000000;
  uart_set_cfg(0,(test_freq/baud_rate)>>4);

  int volatile  * ptr;
  int buff,b;
  int err = 0;
  for(int i = 0; i<100; i++){
    ptr = (int *) TCDM_BASE + i*4;
    *ptr = i;
  }
  ptr = (int *) (IDMA_BASE + IDMA_SRC_ADDR_OFFSET);
  *ptr = TCDM_BASE;
  ptr = (int *) (IDMA_BASE + IDMA_DST_ADDR_OFFSET);
  *ptr = L2_BASE;
  ptr = (int *) (IDMA_BASE + IDMA_LENGTH_OFFSET);
  *ptr = 0x00000190;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  *ptr = 0x00000001;
  ptr = (int *) (IDMA_BASE);
  *ptr = 0x00000400;
  ptr = (int *) (IDMA_BASE + IDMA_REPS_2_OFFSET);
  *ptr = 0x00000320;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  buff = *ptr;
  for(int i = 0; i<100; i++){
    ptr = (int *) L2_BASE + i;
    b = *ptr;
    if(b=!i){
      printf("Wrong! Reading at 0x%x: 0x%x\r\n",ptr,*ptr);
      uart_wait_tx_done();
      err++;
    }
    else{
      printf("Correct! Reading at 0x%x: 0x%x\r\n",ptr,*ptr);
      uart_wait_tx_done();
    }
  }
  printf("Num errors: %d out of 100!\r\n",err);
  uart_wait_tx_done();
  return 0;
}
