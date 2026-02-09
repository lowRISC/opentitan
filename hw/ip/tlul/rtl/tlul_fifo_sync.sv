// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// TL-UL fifo, used to add elasticity or an asynchronous clock crossing
// to an TL-UL bus.  This instantiates two FIFOs, one for the request side,
// and one for the response side.

module tlul_fifo_sync #(
  parameter bit          ReqPass = 1'b1,
  parameter bit          RspPass = 1'b1,
  parameter int unsigned ReqDepth = 2,
  parameter int unsigned RspDepth = 2,
  parameter int unsigned SpareReqW = 1,
  parameter int unsigned SpareRspW = 1
) (
  input                     clk_i,
  input                     rst_ni,
  input  tlul_pkg::tl_h2d_t tl_h_i,
  output tlul_pkg::tl_d2h_t tl_h_o,
  output tlul_pkg::tl_h2d_t tl_d_o,
  input  tlul_pkg::tl_d2h_t tl_d_i,
  input  [SpareReqW-1:0]    spare_req_i,
  output [SpareReqW-1:0]    spare_req_o,
  input  [SpareRspW-1:0]    spare_rsp_i,
  output [SpareRspW-1:0]    spare_rsp_o
);

  // Put everything on the request side into two FIFOs.
  // The first FIFO holds all data except the integrity bits of the `a_user` field. The second FIFO
  // only holds the command and data integrity bits of the `a_user` field. This is a FI
  // countermeasure, as a fault into one of the two FIFOs will trigger an integrity error once the
  // integrity bits are checked.
  localparam int unsigned REQFIFO_INTG_WIDTH = tlul_pkg::H2DCmdIntgWidth + tlul_pkg::DataIntgWidth;
  localparam int unsigned REQFIFO_WIDTH = $bits(tlul_pkg::tl_h2d_t) -2 + SpareReqW -
                                            REQFIFO_INTG_WIDTH;

  prim_fifo_sync #(.Width(REQFIFO_WIDTH), .Pass(ReqPass), .Depth(ReqDepth)) reqfifo (
    .clk_i,
    .rst_ni,
    .clr_i         (1'b0          ),
    .wvalid_i      (tl_h_i.a_valid),
    .wready_o      (tl_h_o.a_ready),
    .wdata_i       ({tl_h_i.a_opcode,
                     tl_h_i.a_param,
                     tl_h_i.a_size,
                     tl_h_i.a_source,
                     tl_h_i.a_address,
                     tl_h_i.a_mask,
                     tl_h_i.a_data,
                     tl_h_i.a_user.rsvd,
                     tl_h_i.a_user.instr_type,
                     spare_req_i}),
    .rvalid_o      (tl_d_o.a_valid),
    .rready_i      (tl_d_i.a_ready),
    .rdata_o       ({tl_d_o.a_opcode,
                     tl_d_o.a_param,
                     tl_d_o.a_size,
                     tl_d_o.a_source,
                     tl_d_o.a_address,
                     tl_d_o.a_mask,
                     tl_d_o.a_data,
                     tl_d_o.a_user.rsvd,
                     tl_d_o.a_user.instr_type,
                     spare_req_o}),
    .full_o        (),
    .depth_o       (),
    .err_o         ());

  prim_fifo_sync #(.Width(REQFIFO_INTG_WIDTH), .Pass(ReqPass), .Depth(ReqDepth)) reqfifo_intg (
    .clk_i,
    .rst_ni,
    .clr_i         (1'b0          ),
    .wvalid_i      (tl_h_i.a_valid),
    .wready_o      (),
    .wdata_i       ({tl_h_i.a_user.cmd_intg,
                     tl_h_i.a_user.data_intg}),
    .rvalid_o      (),
    .rready_i      (tl_d_i.a_ready),
    .rdata_o       ({tl_d_o.a_user.cmd_intg,
                     tl_d_o.a_user.data_intg}),
    .full_o        (),
    .depth_o       (),
    .err_o         ());

  // Put everything on the response side into the other two FIFOs.
  // The integrity bits and all other bits are separated into two different FIFOs for the same
  // reason as above.
  localparam int unsigned RSPFIFO_INTG_WIDTH = $bits(tlul_pkg::tl_d_user_t);
  localparam int unsigned RSPFIFO_WIDTH = $bits(tlul_pkg::tl_d2h_t) -2 + SpareRspW -
                                            RSPFIFO_INTG_WIDTH;

  prim_fifo_sync #(.Width(RSPFIFO_WIDTH), .Pass(RspPass), .Depth(RspDepth)) rspfifo (
    .clk_i,
    .rst_ni,
    .clr_i         (1'b0          ),
    .wvalid_i      (tl_d_i.d_valid),
    .wready_o      (tl_d_o.d_ready),
    .wdata_i       ({tl_d_i.d_opcode,
                     tl_d_i.d_param ,
                     tl_d_i.d_size  ,
                     tl_d_i.d_source,
                     tl_d_i.d_sink  ,
                     (tl_d_i.d_opcode == tlul_pkg::AccessAckData) ? tl_d_i.d_data :
                                                                    {top_pkg::TL_DW{1'b0}} ,
                     tl_d_i.d_error ,
                     spare_rsp_i}),
    .rvalid_o      (tl_h_o.d_valid),
    .rready_i      (tl_h_i.d_ready),
    .rdata_o       ({tl_h_o.d_opcode,
                     tl_h_o.d_param ,
                     tl_h_o.d_size  ,
                     tl_h_o.d_source,
                     tl_h_o.d_sink  ,
                     tl_h_o.d_data  ,
                     tl_h_o.d_error ,
                     spare_rsp_o}),
    .full_o        (),
    .depth_o       (),
    .err_o         ());

  prim_fifo_sync #(.Width(RSPFIFO_INTG_WIDTH), .Pass(RspPass), .Depth(RspDepth)) rspfifo_intg (
    .clk_i,
    .rst_ni,
    .clr_i         (1'b0          ),
    .wvalid_i      (tl_d_i.d_valid),
    .wready_o      (),
    .wdata_i       (tl_d_i.d_user),
    .rvalid_o      (),
    .rready_i      (tl_h_i.d_ready),
    .rdata_o       (tl_h_o.d_user),
    .full_o        (),
    .depth_o       (),
    .err_o         ());

endmodule
