// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Tile-Link UL adapter for flash-like devices
 *
 */
module tlul_adapter_flash #(
  parameter Outstanding = 1
) (
  input   clk_i,
  input   rst_ni,

  // TL-UL interface
  input   tlul_pkg::tl_h2d_t  tl_i,
  output  tlul_pkg::tl_d2h_t  tl_o,

  // Flash interface
  output logic          req_o,
  input                 req_rdy_i,
  input                 req_done_i,
  output logic [top_pkg::FLASH_AW-1:0] addr_o,
  input        [top_pkg::FLASH_DW-1:0] rdata_i
);

  localparam int DataBitWidth = $clog2(top_pkg::FLASH_BYTES_PER_WORD);
  localparam int TotalBitWidth = DataBitWidth + top_pkg::FLASH_AW;

  import tlul_pkg::*;

  typedef struct packed {
    tl_a_op_e                   req_op;
    logic [top_pkg::TL_SZW-1:0] req_size;
    logic [top_pkg::TL_AIW-1:0] req_source;
  } txn_attr_t ;

  typedef struct packed {
    txn_attr_t                    req_attr;
    logic [top_pkg::FLASH_AW-1:0] req_address;
  } req_t ;

  typedef struct packed {
    logic [top_pkg::TL_DW-1:0]  rsp_data;
    logic                       rsp_err;
    logic [top_pkg::TL_SZW-1:0] rsp_size;
    logic [top_pkg::TL_AIW-1:0] rsp_source;
  } rsp_t ;

  localparam int ReqFifoWidth = $bits(req_t) ;
  localparam int RspFifoWidth = $bits(rsp_t) ;

  req_t reqfifo_wdata, reqfifo_rdata;
  rsp_t rspfifo_wdata, rspfifo_rdata;
  logic reqfifo_rvalid;
  logic rspfifo_wready;
  txn_attr_t req_attr;

  assign reqfifo_wdata.req_attr.req_op = tl_i.a_opcode;
  assign reqfifo_wdata.req_attr.req_size = tl_i.a_size;
  assign reqfifo_wdata.req_attr.req_source = tl_i.a_source;
  assign reqfifo_wdata.req_address = tl_i.a_address[DataBitWidth +: top_pkg::FLASH_AW];


  // REQ FIFO
  prim_fifo_sync #(
    .Width  (ReqFifoWidth),
    .Pass   (1'b1),
    .Depth  (Outstanding)
  ) u_reqfifo (
    .clk_i,
    .rst_ni,
    .wvalid (tl_i.a_valid),
    .wready (tl_o.a_ready),
    .wdata  (reqfifo_wdata),
    .depth  (),
    .rvalid (reqfifo_rvalid),
    .rready (req_o & req_rdy_i),
    .rdata  (reqfifo_rdata)
  );

  // The FIFO above immediately pushes to the next entry when request is accepted
  // This is to ensure back to back reads can happen without a command gap.  So the
  // request attributes need to be separately saved for the response path
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      req_attr.req_op <= Get;
      req_attr.req_size <= {top_pkg::TL_SZW{1'b0}};
      req_attr.req_source <= {top_pkg::TL_AIW{1'b0}};
    end else if(req_o && req_rdy_i) begin
      req_attr <= reqfifo_rdata.req_attr;
    end
  end

  assign rspfifo_wdata.rsp_data = rdata_i;
  assign rspfifo_wdata.rsp_err = req_attr.req_op != Get;
  assign rspfifo_wdata.rsp_size = req_attr.req_size;
  assign rspfifo_wdata.rsp_source = req_attr.req_source;

  // RSP FIFO
  prim_fifo_sync #(
    .Width  (RspFifoWidth),
    .Pass   (1'b1),
    .Depth  (Outstanding)
  ) u_rspfifo (
    .clk_i,
    .rst_ni,
    .wvalid (req_done_i),
    .wready (rspfifo_wready),
    .wdata  (rspfifo_wdata),
    .depth  (),
    .rvalid (tl_o.d_valid),
    .rready (tl_i.d_ready),
    .rdata  (rspfifo_rdata)
  );


  // assignments to tlul interface
  assign tl_o.d_opcode = AccessAckData;
  assign tl_o.d_param  = '0;
  assign tl_o.d_size   = rspfifo_rdata.rsp_size;
  assign tl_o.d_source = rspfifo_rdata.rsp_source;
  assign tl_o.d_sink   = 1'b0;
  assign tl_o.d_data   = rspfifo_rdata.rsp_data;
  assign tl_o.d_user   = '0;
  assign tl_o.d_error  = rspfifo_rdata.rsp_err;

  //assignments to flash interface
  assign req_o = reqfifo_rvalid & rspfifo_wready;
  assign addr_o = reqfifo_rdata.req_address;

  //unused interface
  logic [top_pkg::TL_DW-1:0] unused_data;
  logic [top_pkg::TL_DBW-1:0] unused_mask;
  logic [2:0] unused_param;
  logic [top_pkg::TL_DUW-1:0] unused_user;
  logic [DataBitWidth-1:0] unused_low_addr;
  logic [top_pkg::TL_DW - TotalBitWidth - 1:0] unused_high_addr;

  assign unused_data = tl_i.a_data;
  assign unused_mask = tl_i.a_mask;
  assign unused_param = tl_i.a_param;
  assign unused_user = tl_i.a_user;
  assign unused_low_addr = tl_i.a_address[DataBitWidth-1:0];
  assign unused_high_addr = tl_i.a_address[top_pkg::TL_DW-1 : TotalBitWidth];

endmodule
