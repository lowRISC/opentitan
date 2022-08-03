// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// TL-UL fifo, used to add elasticity or an asynchronous clock crossing
// to an TL-UL bus.  This instantiates two FIFOs, one for the request side,
// and one for the response side.

`include "prim_assert.sv"

module tlul_fifo_async #(
  parameter int unsigned ReqDepth = 3,
  parameter int unsigned RspDepth = 3
) (
  input                      clk_h_i,
  input                      rst_h_ni,
  input                      clk_d_i,
  input                      rst_d_ni,
  input  tlul_pkg::tl_h2d_t  tl_h_i,
  output tlul_pkg::tl_d2h_t  tl_h_o,
  output tlul_pkg::tl_h2d_t  tl_d_o,
  input  tlul_pkg::tl_d2h_t  tl_d_i
);

  // Put everything on the request side into one FIFO
  localparam int unsigned REQFIFO_WIDTH = $bits(tlul_pkg::tl_h2d_t)-2;

  prim_fifo_async #(
    .Width(REQFIFO_WIDTH),
    .Depth(ReqDepth),
    .OutputZeroIfInvalid(1)
  ) reqfifo (
    .clk_wr_i      (clk_h_i),
    .rst_wr_ni     (rst_h_ni),
    .clk_rd_i      (clk_d_i),
    .rst_rd_ni     (rst_d_ni),
    .wvalid_i      (tl_h_i.a_valid),
    .wready_o      (tl_h_o.a_ready),
    .wdata_i       ({tl_h_i.a_opcode ,
                     tl_h_i.a_param  ,
                     tl_h_i.a_size   ,
                     tl_h_i.a_source ,
                     tl_h_i.a_address,
                     tl_h_i.a_mask   ,
                     tl_h_i.a_data   ,
                     tl_h_i.a_user   }),
    .rvalid_o      (tl_d_o.a_valid),
    .rready_i      (tl_d_i.a_ready),
    .rdata_o       ({tl_d_o.a_opcode ,
                     tl_d_o.a_param  ,
                     tl_d_o.a_size   ,
                     tl_d_o.a_source ,
                     tl_d_o.a_address,
                     tl_d_o.a_mask   ,
                     tl_d_o.a_data   ,
                     tl_d_o.a_user   }),
    .wdepth_o      (),
    .rdepth_o      ()
  );

  // Put everything on the response side into the other FIFO

  localparam int unsigned RSPFIFO_WIDTH = $bits(tlul_pkg::tl_d2h_t) -2;

  prim_fifo_async #(
    .Width(RSPFIFO_WIDTH),
    .Depth(RspDepth),
    .OutputZeroIfInvalid(1)
  ) rspfifo (
    .clk_wr_i      (clk_d_i),
    .rst_wr_ni     (rst_d_ni),
    .clk_rd_i      (clk_h_i),
    .rst_rd_ni     (rst_h_ni),
    .wvalid_i      (tl_d_i.d_valid),
    .wready_o      (tl_d_o.d_ready),
    .wdata_i       ({tl_d_i.d_opcode,
                     tl_d_i.d_param ,
                     tl_d_i.d_size  ,
                     tl_d_i.d_source,
                     tl_d_i.d_sink  ,
                     tl_d_i.d_data  ,
                     tl_d_i.d_user  ,
                     tl_d_i.d_error }),
    .rvalid_o      (tl_h_o.d_valid),
    .rready_i      (tl_h_i.d_ready),
    .rdata_o       ({tl_h_o.d_opcode,
                     tl_h_o.d_param ,
                     tl_h_o.d_size  ,
                     tl_h_o.d_source,
                     tl_h_o.d_sink  ,
                     tl_h_o.d_data  ,
                     tl_h_o.d_user  ,
                     tl_h_o.d_error }),
    .wdepth_o      (),
    .rdepth_o      ()
  );

endmodule
