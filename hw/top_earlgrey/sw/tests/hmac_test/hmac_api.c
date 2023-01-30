// Copyright (c) 2022 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// Copyright (c) 2022 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
//

bool hmac_init(void) {

   int volatile * hmac;
   
   // shodow register setup: manual mode
   hmac = (int *) 0xc1110010;
  *hmac = 0x3;

   hmac = (int *) 0xc1110014;
  *hmac = 0x1;

   return true;
}


bool hmac_write_key(void) {
  
   int volatile * hmac;
   int a=0;

   // writing crypto key
   hmac = (int *) 0xc1110024;
  *hmac = 0x94823467;

   hmac = (int *) 0xc1110028;
  *hmac = 0x94823467;

   hmac = (int *) 0xc111002C;
  *hmac = 0x94823467;

   hmac = (int *) 0xc1110030;
  *hmac = 0x94823467;

   hmac = (int *) 0xc1110034;
  *hmac = 0x94823467;

   hmac = (int *) 0xc1110038;
  *hmac = 0x94823467;

   hmac = (int *) 0xc111003C;
  *hmac = 0x94823467;

   hmac = (int *) 0xc1110040;
  *hmac = 0x94823467;

   return true;

}


bool hmac_input_mbox (void) {

   int volatile * hmac_1, * hmac_2, * hmac_3, * hmac_4;
   int volatile * mbox_1, * mbox_2, * mbox_3, * mbox_4;
   
   mbox_1 = (int *) 0x10404000;
   mbox_2 = (int *) 0x10404004;
   mbox_3 = (int *) 0x10404008;
   mbox_4 = (int *) 0x1040400C;

   hmac_1 = (int *) 0xc1110800;
   hmac_2 = (int *) 0xc1110804;
   hmac_3 = (int *) 0xc1110808;
   hmac_4 = (int *) 0xc111080C;
   
  *hmac_1 = *mbox_1;
  *hmac_2 = *mbox_2;
  *hmac_3 = *mbox_3;
  *hmac_4 = *mbox_4;

   return true;
}

bool hmac_input_ibex (void) {

   int volatile * hmac_1, * hmac_2, * hmac_3, * hmac_4;
   int volatile * ibex_1, * ibex_2, * ibex_3, * ibex_4;
   
   ibex_1 = (int *) 0xe000F000;
   ibex_2 = (int *) 0xe000F004;
   ibex_3 = (int *) 0xe000F008;
   ibex_4 = (int *) 0xe000F00C;

   hmac_1 = (int *) 0xc1110800;
   hmac_2 = (int *) 0xc1110804;
   hmac_3 = (int *) 0xc1110808;
   hmac_4 = (int *) 0xc111080C;
   
  *hmac_1 = *ibex_1;
  *hmac_2 = *ibex_2;
  *hmac_3 = *ibex_3;
  *hmac_4 = *ibex_4;

   return true;
}

bool hmac_input_ariane (void) {

   int volatile * hmac_1, * hmac_2, * hmac_3, * hmac_4;
   int volatile * ariane_1, * ariane_2, * ariane_3, * ariane_4;
   
   ariane_1 = (int *) 0x1C000800;
   ariane_2 = (int *) 0x1C000804;
   ariane_3 = (int *) 0x1C000808;
   ariane_4 = (int *) 0x1C00080C;

   hmac_1 = (int *) 0xc1110800;
   hmac_2 = (int *) 0xc1110804;
   hmac_3 = (int *) 0xc1110808;
   hmac_4 = (int *) 0xc111080C;
   
  *hmac_1 = *ariane_1;
  *hmac_2 = *ariane_2;
  *hmac_3 = *ariane_3;
  *hmac_4 = *ariane_4;

   return true;
}

bool hmac_input_hyper (void) {

   int volatile * hmac_1, * hmac_2, * hmac_3, * hmac_4;
   int volatile * hyper_1, * hyper_2, * hyper_3, * hyper_4;
   
   hyper_1 = (int *) 0x80010800;
   hyper_2 = (int *) 0x80010804;
   hyper_3 = (int *) 0x80010808;
   hyper_4 = (int *) 0x8001080C;

   hmac_1 = (int *) 0xc1110800;
   hmac_2 = (int *) 0xc1110804;
   hmac_3 = (int *) 0xc1110808;
   hmac_4 = (int *) 0xc111080C;
   
  *hmac_1 = *hyper_1;
  *hmac_2 = *hyper_2;
  *hmac_3 = *hyper_3;
  *hmac_4 = *hyper_4;

   return true;
}

bool hmac_encrypt(void) {

   int volatile * hmac;
   int a = 0;
   
   // trigger encryption
   hmac = (int *) 0xc1110014;
  *hmac = 0x3;

   hmac = (int *) 0xc1110000;
   while(a != 0x7)
     a = *hmac;
   a = 0;

   return true;
}

bool entropy_init(void) {
  
  int volatile * edn_enable, * csrng_enable, * entropy_src_enable;

  entropy_src_enable = (int *) 0xc1160024;
 *entropy_src_enable = 0x00909099;

  entropy_src_enable = (int *) 0xc1160020;
 *entropy_src_enable = 0x6;

  csrng_enable = (int *) 0xc1150014;
 *csrng_enable = 0x666;

  edn_enable = (int *) 0xc1170014;
 *edn_enable = 0x9966;

  return true;
}

bool preload_mbox(void){

  int * mbox_pointer;

  mbox_pointer = (int *) 0x10404000;
 *mbox_pointer = 0xbadcab1e;

  mbox_pointer = (int *) 0x10404004;
 *mbox_pointer = 0xbadcab1e;

  mbox_pointer = (int *) 0x10404008;
 *mbox_pointer = 0xbadcab1e;

  mbox_pointer = (int *) 0x1040400C;
 *mbox_pointer = 0xbadcab1e;

  return true;

}

bool preload_ibex(void){

  int * ibex_pointer;

  ibex_pointer = (int *) 0xe000F000;
 *ibex_pointer = 0xbadcab1e;

  ibex_pointer = (int *) 0xe000F004;
 *ibex_pointer = 0xbadcab1e;

  ibex_pointer = (int *) 0xe000F008;
 *ibex_pointer = 0xbadcab1e;

  ibex_pointer = (int *) 0xe000F00C;
 *ibex_pointer = 0xbadcab1e;

  return true;

}

bool preload_ariane(void){

  int * ariane_pointer;

  ariane_pointer = (int *) 0x1C000800;
 *ariane_pointer = 0xbadcab1e;

  ariane_pointer = (int *) 0x1C000804;
 *ariane_pointer = 0xbadcab1e;

  ariane_pointer = (int *) 0x1C000808;
 *ariane_pointer = 0xbadcab1e;

  ariane_pointer = (int *) 0x1C00080C;
 *ariane_pointer = 0xbadcab1e;

  return true;

}

bool preload_hyper(void){

  int * hyper_pointer;

  hyper_pointer = (int *) 0x80010800;
 *hyper_pointer = 0xbadcab1e;

  hyper_pointer = (int *) 0x80010804;
 *hyper_pointer = 0xbadcab1e;

  hyper_pointer = (int *) 0x80010808;
 *hyper_pointer = 0xbadcab1e;

  hyper_pointer = (int *) 0x8001080C;
 *hyper_pointer = 0xbadcab1e;

  return true;

}

bool hmac_read_out(void){

   int volatile * hmac;
   int a,b,c,d,e,f,g,h;
   
   // writing crypto key
   hmac = (int *) 0xc1110044;
   a = *hmac;
   //printf("%d",a);

   hmac = (int *) 0xc1110048;
   b = *hmac;
   //printf("%d",b);
   
   hmac = (int *) 0xc111004C;
   c = *hmac;
   //printf("%d",c);

   hmac = (int *) 0xc1110050;
   d = *hmac;
   //printf("%d",d);

   hmac = (int *) 0xc1110054;
   e = *hmac;
   //printf("%d",e);

   hmac = (int *) 0xc1110058;
   f = *hmac;
   //printf("%d",f);

   hmac = (int *) 0xc111005C;
   g = *hmac;
   //printf("%d",g);

   hmac = (int *) 0xc1110060;
   h = *hmac;
   //printf("%d",h);
   
   //printf("\r\n");

   //printf("Key: %d%d%d%d%d%d%d%d\r\n", a,b,c,d,e,f,g,h);

   return true;

}

