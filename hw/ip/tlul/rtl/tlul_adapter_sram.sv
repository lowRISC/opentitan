// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Tile-Link UL adapter for SRAM-like devices
 *
 * - Intentionally omitted BaseAddr in case of multiple memory maps are used in a SoC,
 *   it means that aliasing can happen if target slave size in TL-UL crossbar is bigger
 *   than SRAM size
 */
module tlul_adapter_sram #(
  parameter int SramAw      = 12,
  parameter int SramDw      = 32, // Current version supports TL-UL width only
  parameter int Outstanding = 1,  // Only one request is accepted
  parameter bit ByteAccess  = 1   // 1: true, 0: false
) (
  input   clk_i,
  input   rst_ni,

  // TL-UL interface
  input   tlul_pkg::tl_h2d_t  tl_i,
  output  tlul_pkg::tl_d2h_t  tl_o,

  // SRAM interface
  output logic              req_o,
  input                     gnt_i,
  output logic              we_o,
  output logic [SramAw-1:0] addr_o,
  output logic [SramDw-1:0] wdata_o,
  output logic [SramDw-1:0] wmask_o,
  input        [SramDw-1:0] rdata_i,
  input                     rvalid_i,
  input        [1:0]        rerror_i // 2 bit error [1]: Uncorrectable, [0]: Correctable
);

  import tlul_pkg::*;

  localparam int SramByte = SramDw/8; // TODO: Fatal if SramDw isn't multiple of 8
  localparam int DataBitWidth = $clog2(SramByte);

  typedef struct packed {
    logic                       op ;
    logic                       wrsp_error ;
    logic [top_pkg::TL_SZW-1:0] size ;
    logic [top_pkg::TL_AIW-1:0] source ;
  } req_t ;

  typedef struct packed {
    logic [SramDw-1:0] data ;
    logic              error ;
  } rsp_t ;

  localparam int ReqFifoWidth = $bits(req_t) ;
  localparam int RspFifoWidth = $bits(rsp_t) ;

  // FIFO signal in case OutStand is greater than 1
  // If request is latched, {write, source} is pushed to req fifo.
  // Req fifo is popped when D channel is acknowledged (v & r)
  // D channel valid is asserted if it is write request or rsp fifo not empty if read.
  logic reqfifo_wvalid, reqfifo_wready;
  logic reqfifo_rvalid, reqfifo_rready;
  req_t reqfifo_wdata,  reqfifo_rdata;

  logic rspfifo_wvalid, rspfifo_wready;
  logic rspfifo_rvalid, rspfifo_rready;
  rsp_t rspfifo_wdata,  rspfifo_rdata;

  logic wrsp_error;

  assign tl_o = '{
      d_valid  : reqfifo_rdata.op ? reqfifo_rvalid : rspfifo_rvalid ,
      d_opcode : reqfifo_rdata.op ? AccessAck : AccessAckData ,
      d_param  : '0,
      d_size   : reqfifo_rdata.size,
      d_source : reqfifo_rdata.source,
      d_sink   : 1'b0,
      d_data   : rspfifo_rdata.data,
      d_user   : '0,
      d_error  : reqfifo_rdata.op ? reqfifo_rdata.wrsp_error : rspfifo_rdata.error,

      a_ready  : gnt_i & reqfifo_wready
  };

  // a_ready depends on the FIFO full condition and grant from SRAM (or SRAM arbiter)
  // assemble response, including read response, write response, and error for unsupported stuff

  assign req_o    = reqfifo_wready & tl_i.a_valid;
  assign we_o     = (tl_i.a_opcode == PutFullData || tl_i.a_opcode == PutPartialData) ? 1'b1 : 1'b0;
  assign addr_o   = tl_i.a_address[DataBitWidth+:SramAw];
  assign wdata_o  = tl_i.a_data;

  if (top_pkg::TL_DW == SramDw) begin : gen_wmask
    always_comb begin
      for (int i = 0 ; i < top_pkg::TL_DW/8 ; i++) begin
        wmask_o[8*i+:8] = {8{tl_i.a_mask[i]}};
      end
    end
  end else begin : gen_err_wmask
    $fatal("Current TL-UL SRAM adapter only supports the case of SramDw == TL_DW");
  end

  if (ByteAccess == 1) begin : gen_wrsp_byte
    assign wrsp_error = (tl_i.a_opcode == PutFullData &&
                        (tl_i.a_mask != '1 || tl_i.a_size != 2'h2));
  end else begin : gen_wrsp_word
    assign wrsp_error = (tl_i.a_mask != '1 || tl_i.a_size != 2'h2);
  end

  // TODO: handle rvalid
  assign reqfifo_wvalid = req_o && gnt_i ;
  assign reqfifo_wdata  = '{
    op: we_o,
    wrsp_error: wrsp_error,
    size: tl_i.a_size,
    source: tl_i.a_source
  }; // Store the request only. Doesn't have to store data
  assign reqfifo_rready = tl_o.d_valid & tl_i.d_ready ;

  assign rspfifo_wvalid = rvalid_i ;
  assign rspfifo_wdata  = '{
    data:  rdata_i,
    error: rerror_i[1]  // Only care for Uncorrectable error
  };
  assign rspfifo_rready = ~reqfifo_rdata.op & reqfifo_rready ;

  // FIFO instance: REQ, RSP
  prim_fifo_sync #(
    .Width  (ReqFifoWidth),
    .Pass   (1'b0),
    .Depth  (Outstanding)
  ) u_reqfifo (
    .clk_i,
    .rst_ni,
    .wvalid (reqfifo_wvalid),
    .wready (reqfifo_wready),
    .wdata  (reqfifo_wdata),
    .depth  (),
    .rvalid (reqfifo_rvalid),
    .rready (reqfifo_rready),
    .rdata  (reqfifo_rdata)
  );

  prim_fifo_sync #(
    .Width (RspFifoWidth),
    .Pass  (1'b0),
    .Depth (Outstanding)
  ) u_rspfifo (
    .clk_i,
    .rst_ni,
    .wvalid (rspfifo_wvalid),
    .wready (rspfifo_wready),
    .wdata  (rspfifo_wdata),
    .depth  (),
    .rvalid (rspfifo_rvalid),
    .rready (rspfifo_rready),
    .rdata  (rspfifo_rdata)
  );

  // below assertion fails when SRAM rvalid is asserted even though ReqFifo is empty
  `ASSERT(rvalidHighReqFifoEmpty, rvalid_i |-> reqfifo_rvalid, clk_i, !rst_ni)

  // below assertion fails when outstanding value is too small (SRAM rvalid is asserted
  // even though the RspFifo is full)
  `ASSERT(rvalidHighWhenRspFifoFull, rvalid_i |-> rspfifo_wready, clk_i, !rst_ni)

endmodule
