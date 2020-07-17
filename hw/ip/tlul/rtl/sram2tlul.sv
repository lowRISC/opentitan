// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SRAM interface to TL-UL converter
//      Current version only supports if TL-UL width and SRAM width are same
//      If SRAM interface requests more than MaxOutstanding cap, it generates
//      error in simulation but not in Silicon.

`include "prim_assert.sv"

module sram2tlul #(
  parameter int                        SramAw = 12,
  parameter int                        SramDw = 32,
  parameter logic [top_pkg::TL_AW-1:0] TlBaseAddr = 'h0  // Base address of SRAM request
) (
  input clk_i,
  input rst_ni,

  output tlul_pkg::tl_h2d_t tl_o,
  input  tlul_pkg::tl_d2h_t tl_i,

  // SRAM
  input                     mem_req_i,
  input                     mem_write_i,
  input        [SramAw-1:0] mem_addr_i,
  input        [SramDw-1:0] mem_wdata_i,
  output logic              mem_rvalid_o,
  output logic [SramDw-1:0] mem_rdata_o,
  output logic        [1:0] mem_error_o
);

  import tlul_pkg::*;

  `ASSERT_INIT(wrongSramDw, SramDw == top_pkg::TL_DW)

  localparam int unsigned SRAM_DWB = $clog2(SramDw/8);

  assign tl_o.a_valid   = mem_req_i;
  assign tl_o.a_opcode  = (mem_write_i) ? PutFullData : Get;
  assign tl_o.a_param   = '0;
  assign tl_o.a_size    = top_pkg::TL_SZW'(SRAM_DWB); // Max Size always
  assign tl_o.a_source  = '0;
  assign tl_o.a_address = TlBaseAddr |
                          {{(top_pkg::TL_AW-SramAw-SRAM_DWB){1'b0}},mem_addr_i,{(SRAM_DWB){1'b0}}};
  assign tl_o.a_mask    = '1;
  assign tl_o.a_data    = mem_wdata_i;
  assign tl_o.a_user    = '0;

  assign tl_o.d_ready   = 1'b1;

  assign mem_rvalid_o   = tl_i.d_valid && (tl_i.d_opcode == AccessAckData);
  assign mem_rdata_o    = tl_i.d_data;
  assign mem_error_o    = {2{tl_i.d_error}};

  // below assertion fails when TL-UL doesn't accept request in a cycle,
  // which is currently not supported by sram2tlul
  `ASSERT(validNotReady, tl_o.a_valid |-> tl_i.a_ready)

endmodule
