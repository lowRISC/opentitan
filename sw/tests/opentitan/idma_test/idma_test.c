#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"

#define IDMA_BASE 		 0xfef00000
#define TCDM_BASE      0xfff00000
#define L2_BASE        0x1C001000
#define L3_BASE        0x80000000

#define IDMA_SRC_ADDR_OFFSET         0x000000d8
#define IDMA_DST_ADDR_OFFSET         0x000000d0
#define IDMA_LENGTH_OFFSET           0x000000e0
#define IDMA_NEXT_ID_OFFSET          0x00000044
#define IDMA_REPS_2                  0x000000f8
#define IDMA_REPS_3                  0x00000110
#define IDMA_CONF                    0x00000000
#define EOC                          0xc11c0018

int main() {

  int volatile  * ptr;
  int buff,b;
  int err = 0;

  for(int i = 0; i<1024; i++){
    ptr = (int *) TCDM_BASE + i*4;
    *ptr = i;
  }

  ptr = (int *) (IDMA_BASE + IDMA_SRC_ADDR_OFFSET);
  *ptr = TCDM_BASE;
  ptr = (int *) (IDMA_BASE + IDMA_DST_ADDR_OFFSET);
  *ptr = L2_BASE;
  ptr = (int *) (IDMA_BASE + IDMA_LENGTH_OFFSET);
  *ptr = 0x00000190;
  ptr = (int *) (IDMA_BASE + IDMA_CONF);
  *ptr = 0x3<<10;
  ptr = (int *) (IDMA_BASE + IDMA_REPS_2);
  *ptr = 0x00000001;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  buff = *ptr;

  for(int i = 0; i<1024; i++){
    ptr = (int *) L2_BASE + i;
    b = *ptr;
    if(b=!i)
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
