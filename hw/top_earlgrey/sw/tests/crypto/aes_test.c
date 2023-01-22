// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

bool crypto_test_main(void) {
  
   int volatile * aes;
   int a=0;
   
   aes = (int *) 0xc1100084;
   while ( a != 0x11)
     a = *aes;

   a=0;
   
   // shodow register setup: manual mode
   aes = (int *) 0xc1100074; 
  *aes = 0xC905;
  *aes = 0xC905;
   ///////////////////////

   // writing crypto key
   aes = (int *) 0xc1100004;
  *aes = 0x94823467;

   aes = (int *) 0xc1100008;
  *aes = 0x94823467;

   aes = (int *) 0xc110000C;
  *aes = 0x94823467;

   aes = (int *) 0xc1100010;
  *aes = 0x94823467;

   aes = (int *) 0xc1100014;
  *aes = 0x94823467;

   aes = (int *) 0xc1100018;
  *aes = 0x94823467;

   aes = (int *) 0xc110001C;
  *aes = 0x94823467;

   aes = (int *) 0xc1100020;
  *aes = 0x94823467;

   aes = (int *) 0xc1100024;
  *aes = 0x94823467;

   aes = (int *) 0xc1100028;
  *aes = 0x94823467;

   aes = (int *) 0xc110002C;
  *aes = 0x94823467;

   aes = (int *) 0xc1100030;
  *aes = 0x94823467;

   aes = (int *) 0xc1100034;
  *aes = 0x94823467;

   aes = (int *) 0xc1100038;
  *aes = 0x94823467;
  
   aes = (int *) 0xc110003C;
  *aes = 0x94823467;

   aes = (int *) 0xc1100040;
  *aes = 0x94823467; 
   ///////////////////////

   aes = (int *) 0xc1100084;
   while ( a != 0x11)
     a = *aes;
   a = 0;
   
   // writing input data
   aes = (int *) 0xc1100054;
  *aes = 0x24893753;

   aes = (int *) 0xc1100058;
  *aes = 0x54673456;

   aes = (int *) 0xc110005C;
  *aes = 0x54356546;
  
   aes = (int *) 0xc1100060;
  *aes = 0x54356546;
   ///////////////////////
  /*
   aes = (int *) 0xc1100084;
   while ( a != 0x11)
     a = *aes;
   a = 0;
  */
   // writing input data
   aes = (int *) 0xc1100054;
  *aes = 0x24893325;

   aes = (int *) 0xc1100058;
  *aes = 0x54753245;

   aes = (int *) 0xc110005C;
  *aes = 0x54762356;
  
   aes = (int *) 0xc1100060;
  *aes = 0x54343043;
   ///////////////////////
  
   // trigger encryption
   aes = (int *) 0xc1100080;
  *aes = 0x1;
  
   return true;
}

