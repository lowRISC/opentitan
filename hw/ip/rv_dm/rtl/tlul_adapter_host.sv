// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// tlul_adapter (Host adapter) converts basic req/grant/rvalid into TL-UL
// interface. It doesn't need register but combinational logics.

`include "prim_assert.sv"

module tlul_adapter_host #(
  parameter int unsigned AW = 32,
  parameter int unsigned DW = 32
) (
  input clk_i   ,
  input rst_ni  ,

  input                   req_i   ,
  output logic            gnt_o   ,
  input        [AW-1:0]   addr_i  ,
  input                   we_i    ,
  input        [DW-1:0]   wdata_i ,
  input        [DW/8-1:0] be_i    ,
  input        [1:0]      size_i  , // 2**(size_i)

  output logic            valid_o ,
  output logic [DW-1:0]   rdata_o ,

  output tlul_pkg::tl_h2d_t tl_o ,
  input  tlul_pkg::tl_d2h_t tl_i
);

  tlul_pkg::tl_a_op_e req_op;

  assign req_op = (we_i) ? tlul_pkg::PutFullData : tlul_pkg::Get ;

  assign tl_o = '{
    a_valid:      req_i       ,
    a_opcode:     req_op      ,
    a_param:      '0          ,
    a_size:       size_i      ,
    a_source:     '0          ,
    a_address:    addr_i      ,
    a_mask:       be_i        ,
    a_data:       wdata_i     ,
    a_user:       '0          ,

    d_ready:      1'b1          // Ready to accept
  };

  assign gnt_o   = tl_i.a_ready; // Do we need to and with req_i? then registers are required

  assign valid_o = tl_i.d_valid;
  assign rdata_o = tl_i.d_data;

  // this assertion fails when DBG adapter cannot handle error response
  `ASSERT(handleErrorResponse, tl_i.d_valid |-> (tl_i.d_error == 1'b0))

endmodule
