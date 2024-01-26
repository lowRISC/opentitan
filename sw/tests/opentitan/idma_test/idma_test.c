#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"

#define IDMA_BASE 		 0xfef00000
#define TCDM_BASE      0xfff00000

#define IDMA_SRC_ADDR_OFFSET         0xd8
#define IDMA_DST_ADDR_OFFSET         0xd0
#define IDMA_LENGTH_OFFSET           0xe0
#define IDMA_NEXT_ID_OFFSET          0x44
#define IDMA_REPS_2_OFFSET           0xf8
int main() {

  int volatile  * ptr;
  int buff,b;
  for(int i = 0; i<100; i++){
    ptr = (int *) TCDM_BASE + i*4;
    *ptr = i;
  }
  ptr = (int *) (IDMA_BASE + IDMA_SRC_ADDR_OFFSET);
  *ptr = TCDM_BASE;
  ptr = (int *) (IDMA_BASE + IDMA_DST_ADDR_OFFSET);
  *ptr = 0x10000000;
  ptr = (int *) (IDMA_BASE + IDMA_LENGTH_OFFSET);
  *ptr = 0x00000320;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  *ptr = 0x00000001;
  ptr = (int *) (IDMA_BASE + IDMA_REPS_2_OFFSET);
  *ptr = 0x00000320;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  buff = *ptr;
  for(int i=0;i<100;i++)
    b = i;
  /*ptr = (int *) (IDMA_BASE + IDMA_REPS_2_OFFSET);
  *ptr = 0x00000000;

  ptr = (int *) (IDMA_BASE + IDMA_SRC_ADDR_OFFSET);
  *ptr = 0x10000000;
  ptr = (int *) (IDMA_BASE + IDMA_DST_ADDR_OFFSET);
  *ptr = TCDM_BASE;
  ptr = (int *) (IDMA_BASE + IDMA_LENGTH_OFFSET);
  *ptr = 0x00000320;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  *ptr = 0x00000001;
  ptr = (int *) (IDMA_BASE + IDMA_REPS_2_OFFSET);
  *ptr = 0x00000001;
  ptr = (int *) (IDMA_BASE + IDMA_NEXT_ID_OFFSET);
  buff = *ptr;
  */
  return 0;
}
