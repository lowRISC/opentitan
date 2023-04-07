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

bool aes_init(void) {

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

   return true;
}


bool aes_write_key(void) {
  
   int volatile * aes;
   int a=0;

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

   return true;

}


bool aes_input_mbox (void) {

   int volatile * aes_1, * aes_2, * aes_3, * aes_4;
   int volatile * mbox_1, * mbox_2, * mbox_3, * mbox_4;
   
   mbox_1 = (int *) 0x10404000;
   mbox_2 = (int *) 0x10404004;
   mbox_3 = (int *) 0x10404008;
   mbox_4 = (int *) 0x1040400C;

   aes_1 = (int *) 0xc1100054;
   aes_2 = (int *) 0xc1100058;
   aes_3 = (int *) 0xc110005C;
   aes_4 = (int *) 0xc1100060;
   
  *aes_1 = *mbox_1;
  *aes_2 = *mbox_2;
  *aes_3 = *mbox_3;
  *aes_4 = *mbox_4;

   return true;
}

bool aes_input_ibex (void) {

   int volatile * aes_1, * aes_2, * aes_3, * aes_4;
   int volatile * ibex_1, * ibex_2, * ibex_3, * ibex_4;
   
   ibex_1 = (int *) 0xe000F000;
   ibex_2 = (int *) 0xe000F004;
   ibex_3 = (int *) 0xe000F008;
   ibex_4 = (int *) 0xe000F00C;

   aes_1 = (int *) 0xc1100054;
   aes_2 = (int *) 0xc1100058;
   aes_3 = (int *) 0xc110005C;
   aes_4 = (int *) 0xc1100060;
   
  *aes_1 = *ibex_1;
  *aes_2 = *ibex_2;
  *aes_3 = *ibex_3;
  *aes_4 = *ibex_4;

   return true;
}

bool aes_input_ariane (void) {

   int volatile * aes_1, * aes_2, * aes_3, * aes_4;
   int volatile * ariane_1, * ariane_2, * ariane_3, * ariane_4;
   
   ariane_1 = (int *) 0x1C000800;
   ariane_2 = (int *) 0x1C000804;
   ariane_3 = (int *) 0x1C000808;
   ariane_4 = (int *) 0x1C00080C;

   aes_1 = (int *) 0xc1100054;
   aes_2 = (int *) 0xc1100058;
   aes_3 = (int *) 0xc110005C;
   aes_4 = (int *) 0xc1100060;
   
  *aes_1 = *ariane_1;
  *aes_2 = *ariane_2;
  *aes_3 = *ariane_3;
  *aes_4 = *ariane_4;

   return true;
}

bool aes_input_hyper (void) {

   int volatile * aes_1, * aes_2, * aes_3, * aes_4;
   int volatile * hyper_1, * hyper_2, * hyper_3, * hyper_4;
   
   hyper_1 = (int *) 0x80000800;
   hyper_2 = (int *) 0x80000804;
   hyper_3 = (int *) 0x80000808;
   hyper_4 = (int *) 0x8000080C;

   aes_1 = (int *) 0xc1100054;
   aes_2 = (int *) 0xc1100058;
   aes_3 = (int *) 0xc110005C;
   aes_4 = (int *) 0xc1100060;
   
  *aes_1 = *hyper_1;
  *aes_2 = *hyper_2;
  *aes_3 = *hyper_3;
  *aes_4 = *hyper_4;

   return true;
}

bool aes_encrypt(void) {

   int volatile * aes;
   
   // trigger encryption
   aes = (int *) 0xc1100080;
  *aes = 0x1;

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

  ibex_pointer = (int *) 0xe00F0000;
 *ibex_pointer = 0xbadcab1e;

  ibex_pointer = (int *) 0xe00F0804;
 *ibex_pointer = 0xbadcab1e;

  ibex_pointer = (int *) 0xe00F0808;
 *ibex_pointer = 0xbadcab1e;

  ibex_pointer = (int *) 0xe00F080C;
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

  hyper_pointer = (int *) 0x80000800;
 *hyper_pointer = 0xbadcab1e;

  hyper_pointer = (int *) 0x80000804;
 *hyper_pointer = 0xbadcab1e;

  hyper_pointer = (int *) 0x80000808;
 *hyper_pointer = 0xbadcab1e;

  hyper_pointer = (int *) 0x8000080C;
 *hyper_pointer = 0xbadcab1e;

  return true;

}

bool aes_read_out(void) {
  
   int volatile * aes;
   int j=0;
   int a,b,c,d;
   
   aes = (int *) 0xc1100084;
   while ( j != 0x19)
     j = *aes;
   j = 0;
   
   // reading output data
   aes = (int *) 0xc1100064;
   a = *aes;

   aes = (int *) 0xc1100068;
   b = *aes;

   aes = (int *) 0xc110006C;
   c = *aes;
  
   aes = (int *) 0xc1100070;
   d = *aes;

   aes = (int *) 0xc1100084;
   while ( j != 0x11)
     j = *aes;
   j = 0;
   
   return true;
   
  
}
