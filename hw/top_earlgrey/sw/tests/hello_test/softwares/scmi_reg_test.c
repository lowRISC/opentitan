
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"
#include <stdbool.h>

int main(int argc, char **argv) {

  int a, b, c, d, e;
  int volatile * p_reg, * p_reg1, * p_reg2, * p_reg3, * p_reg4, * p_reg5;
  
  p_reg  = (int *) 0x50000004;

  p_reg1 = (int *) 0x50000008;
  p_reg2 = (int *) 0x50000010;
  p_reg3 = (int *) 0x50000014;
  p_reg4 = (int *) 0x50000018;
  p_reg5 = (int *) 0x5000001C;
  
  while( *p_reg != 0x00000001);

  a = *p_reg1;
  b = *p_reg2;
  c = *p_reg3;
  d = *p_reg4;
  e = *p_reg5;

  if( a == 0xBAADC0DE && b == 0xBAADC0DE && c == 0xBAADC0DE && d == 0xBAADC0DE && e == 0xBAADC0DE){
      p_reg = (int *) 0x50000004;
     *p_reg = 0x00000000;
  }
  else{
     sim_halt();
  }
  
  while(1);
  sim_halt();

  return 0;
}
