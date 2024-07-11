#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
#include "utils.h"
#include "cluster_code.h"

int main() {

  volatile int * ptr;
  ptr = (int *) 0xff000020;
  int lol = load_cluster_code();
  *ptr = 0x1;
  return lol;


}
