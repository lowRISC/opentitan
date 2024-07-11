#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"
#include "cluster_code.h"

//#define CLUSTER_BASE 0x1c000000

int main() {
  /*
  uint32_t volatile  * ptr;

  for(uint32_t i=0;i<buffer_size;i++){
    ptr = (uint32_t *) CLUSTER_BASE + 0x100 + i;
    *ptr = CLUSTER[i];
  }
  */
  int lol = load_cluster_code();
  return lol;

}
