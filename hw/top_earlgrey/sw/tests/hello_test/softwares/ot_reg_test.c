
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "simple_system_common.h"
#include <stdbool.h>

int main(int argc, char **argv) {
  
  int volatile * p_reg, p_reg1, * p_reg2, * p_reg3, * p_reg4, * p_reg5; 
  bool volatile * p_reg_bool;
  bool bit   = true;
  
  char msg1  = '1';
  char msg2  = '2';
  char msg3  = '3';
  char msg4  = '4';
  char msg5  = '5';
  char msg6  = '6';
  char msg7  = '7';
  char msg8  = '8';
  char msg9  = '9';
  char msg10 = 'A';
  char msg11 = 'B';
  char msg12 = 'C';
  char msg13 = 'D';
  char msg14 = 'E';
  char msg15 = 'F';
  char msg16 = 'G';
  int dummy

  ///////////////////////////////////////////////////////////////
  p_reg =(int *) 0x4112002C;
 *p_reg = msg2;
  if(*p_reg == msg2){
    puts("kmac              - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("kmac - failed\n");}
  
  //////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x40130040;
 *p_reg = msg4;
  if(*p_reg == msg4){
    puts("otp               - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("otp        - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x41110004;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("hmac              - succed, msg: true\n"); }
  else{ puts("hmac       - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x40140018;
 *p_reg = msg6;
  if(*p_reg == msg6){
    puts("lc_ctrl           - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("lc_ctrl           - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x411C000C;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("sram_ctrl         - succed, msg:true\n"); }
  else{ puts("sram_ctrl         - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x41000020;
 *p_reg = msg7;
  if(*p_reg == msg7){
    puts("flash_ctrl        - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("flash_ctrl        - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x40000030;
 *p_reg = msg8;
  if(*p_reg == msg8){
    puts("uart              - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("uart              - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x40420000;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("clkmgr            - succed, msg: true\n"); }
  else{ puts("clkmgr            - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x40430004;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("sysrst            - succed, msg: true\n"); }
  else{ puts("sysrst            - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x40410004;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("rstmgr            - succed, msg: true\n"); }
  else{ puts("rstmgr            - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x40400004;
 *p_reg_bool = bit; 
  if(*p_reg_bool == bit){ puts("pwrmgr            - succed, msg: true\n"); }
  else{ puts("pwrmgr            - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x40150004;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("alert_handler     - succed, msg: true\n"); }
  else{ puts("alert_handler     - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg_bool =(bool *) 0x41200000;
 *p_reg_bool = bit;
  if(*p_reg_bool == bit){ puts("rv_dm             - succed, msg: true\n"); }
  else{ puts("rv_dm             - there are no regs\n");}
  

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x4117002C;
 *p_reg = msg10;
  if(*p_reg == msg10){
    puts("edn               - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("edn        - failed\n");}
  
  ///////////////////////////////////////////////////////////////      
    
  p_reg =(int *) 0x41100054;
 *p_reg = msg11;
  if(*p_reg == msg11){
    puts("aes               - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("aes        - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x41150014;
 *p_reg = msg12;
  if(*p_reg == msg12){
    puts("csrng             - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("csrng      - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x4116001C;
 *p_reg = msg13;
  if(*p_reg == msg13){
    puts("entropy_src       - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("entropy_src  - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x40040004;
 *p_reg = msg14;
  if(*p_reg == msg14){
    puts("gpio              - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("gpio  - failed\n");}

  ///////////////////////////////////////////////////////////////
  
  p_reg =(int *) 0x40050050;
 *p_reg = msg15;
  if(*p_reg == msg15){
    puts("spi_device        - succed, msg: ");
    putint(*p_reg);
    puts("\n");
  }
  else{ puts("gpio  - failed\n");}
  
  ///////////////////////////////////////////////////////////////

  // while(1);

  sim_halt();
  return 0;
}
