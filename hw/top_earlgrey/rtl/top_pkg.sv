// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package top_pkg;

localparam int TL_AW=32;
localparam int TL_DW=32;    // = TL_DBW * 8; TL_DBW must be a power-of-two
localparam int TL_AIW=8;    // a_source, d_source
localparam int TL_DIW=1;    // d_sink
localparam int TL_AUW=21;   // a_user
localparam int TL_DUW=14;   // d_user
localparam int TL_DBW=(TL_DW>>3);
localparam int TL_SZW=$clog2($clog2(TL_DBW)+1);
localparam int NUM_AST_ALERTS=7;
localparam int NUM_IO_RAILS=2;
localparam int ENTROPY_STREAM=4;
localparam int ADC_CHANNELS=2;
localparam int ADC_DATAW=10;

`ifdef ANALOGSIM 
  `define INOUT_AI input ast_pkg::awire_t
  `define INOUT_AO output ast_pkg::awire_t
  `define CC1_M '0
  `define CC2_M '0
  `define IOA2_M UC_IOA2
  `define IOA3_M UC_IOA3
  `define IOA4_M '0
  `define IOA5_M '0
`else
  `define INOUT_AI inout
  `define INOUT_AO inout
  `define CC1_M CC1
  `define CC2_M CC2
  `define IOA2_M IOA2
  `define IOA3_M IOA3
  `define IOA4_M IOA4
  `define IOA5_M IOA5
`endif

endpackage
