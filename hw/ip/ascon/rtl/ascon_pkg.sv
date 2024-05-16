// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon package

package ascon_pkg;

parameter logic [63:0] IV_128  = 64'h80400c0600000000;
parameter logic [63:0] IV_128A = 64'h80800c0800000000;

parameter int ASCON_STATE_WIDTH = 320;


parameter int ASCON_OP_WIDTH      = 3;
parameter int ASCON_VARIANT_WIDTH = 2;

typedef enum logic [ASCON_OP_WIDTH-1:0] {
  ASCON_ENC  = 3'b001,
  ASCON_DEC  = 3'b010,
  ASCON_HASH = 3'b100
} ascon_op_e;

typedef enum logic [ASCON_VARIANT_WIDTH-1:0] {
  ASCON_128  = 2'b01,
  ASCON_128A = 2'b10
} ascon_variant_e;

typedef enum logic [11:0] {
  // This encoding represents mubi4True and mubi4False
  MSG_IN = {4'h6, 4'h9, 4'h9},
  AD_IN =  {4'h9, 4'h6, 4'h9},
  TAG_IN = {4'h9, 4'h9, 4'h6},
  NONE =   {4'h9, 4'h9, 4'h9}
} data_type_e;

function automatic logic [127:0] swap_endianess_byte(logic [127:0] vector_in);
  logic [127:0] vector_out;

  // \Verilator does not like this coding style.
  // (and a comment starting with "verilator" or "Verilator"....)
  //
  // for (int i = 0; i < 16; i++) begin
  //   vector_out[127 - 8*i : 120 - 8*i] = vector_in[7 + 8*i : 8*i];
  // end
  //
  // Posible solutions recomend a generate-for-loop and then to embedd an
  // allways_comb block. However this does not seem reasonable for a function.
  // However, there might be other problems:
  //   - https://github.com/verilator/verilator/issues/1418
  //   - https://support.xilinx.com/s/article/55302?language=en_US
  // Thus we do it the old fashion way:

  vector_out[127:120] = vector_in[7:0];
  vector_out[119:112] = vector_in[15:8];
  vector_out[111:104] = vector_in[23:16];
  vector_out[103:96]  = vector_in[31:24];
  vector_out[95:88]   = vector_in[39:32];
  vector_out[87:80]   = vector_in[47:40];
  vector_out[79:72]   = vector_in[55:48];
  vector_out[71:64]   = vector_in[63:56];
  vector_out[63:56]   = vector_in[71:64];
  vector_out[55:48]   = vector_in[79:72];
  vector_out[47:40]   = vector_in[87:80];
  vector_out[39:32]   = vector_in[95:88];
  vector_out[31:24]   = vector_in[103:96];
  vector_out[23:16]   = vector_in[111:104];
  vector_out[15:8]    = vector_in[119:112];
  vector_out[7:0]     = vector_in[127:120];

  return vector_out;
endfunction

endpackage
