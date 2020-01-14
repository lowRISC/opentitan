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

`include "prim_assert.sv"

module tlul_adapter_sram #(
  parameter int SramAw      = 12,
  parameter int SramDw      = 32, // Current version supports TL-UL width only
  parameter int Outstanding = 1,  // Only one request is accepted
  parameter bit ByteAccess  = 1,  // 1: true, 0: false
  parameter bit ErrOnWrite  = 0,  // 1: Writes not allowed, automatically error
  parameter bit ErrOnRead   = 0   // 1: Reads not allowed, automatically error
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

  typedef enum logic [1:0] {
    OpWrite,
    OpRead,
    OpUnknown
  } req_op_e ;

  typedef struct packed {
    req_op_e                    op ;
    logic                       error ;
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

  logic error_internal; // Internal protocol error checker
  logic wr_attr_error;
  logic wr_vld_error;
  logic rd_vld_error;
  logic tlul_error;     // Error from `tlul_err` module

  logic a_ack, d_ack, unused_sram_ack;
  assign a_ack    = tl_i.a_valid & tl_o.a_ready ;
  assign d_ack    = tl_o.d_valid & tl_i.d_ready ;
  assign unused_sram_ack = req_o        & gnt_i ;

  // Valid handling
  logic d_valid, d_error;
  always_comb begin
    d_valid = 1'b0;

    if (reqfifo_rvalid) begin
      if (reqfifo_rdata.error) begin
        // Return error response. Assume no request went out to SRAM
        d_valid = 1'b1;
      end else if (reqfifo_rdata.op == OpRead) begin
        d_valid = rspfifo_rvalid;
      end else begin
        // Write without error
        d_valid = 1'b1;
      end
    end else begin
      d_valid = 1'b0;
    end
  end

  always_comb begin
    d_error = 1'b0;

    if (reqfifo_rvalid) begin
      if (reqfifo_rdata.op == OpRead) begin
        d_error = rspfifo_rdata.error | reqfifo_rdata.error;
      end else begin
        d_error = reqfifo_rdata.error;
      end
    end else begin
      d_error = 1'b0;
    end
  end

  assign tl_o = '{
      d_valid  : d_valid ,
      d_opcode : (d_valid && reqfifo_rdata.op != OpRead) ? AccessAck : AccessAckData,
      d_param  : '0,
      d_size   : (d_valid) ? reqfifo_rdata.size : '0,
      d_source : (d_valid) ? reqfifo_rdata.source : '0,
      d_sink   : 1'b0,
      d_data   : (d_valid && rspfifo_rvalid && reqfifo_rdata.op == OpRead)
                 ? rspfifo_rdata.data : '0,
      d_user   : '0,
      d_error  : d_error,

      a_ready  : (gnt_i | error_internal) & reqfifo_wready
  };

  // a_ready depends on the FIFO full condition and grant from SRAM (or SRAM arbiter)
  // assemble response, including read response, write response, and error for unsupported stuff

  // Output to SRAM:
  //    Generate request only when no internal error occurs. If error occurs, the request should be
  //    dropped and returned error response to the host. So, error to be pushed to reqfifo.
  //    In this case, it is assumed the request is granted (may cause ordering issue later?)
  assign req_o    = tl_i.a_valid & reqfifo_wready & ~error_internal;
  assign we_o     = tl_i.a_valid & logic'(tl_i.a_opcode inside {PutFullData, PutPartialData});
  assign addr_o   = (tl_i.a_valid) ? tl_i.a_address[DataBitWidth+:SramAw] : '0;

  `ASSERT_INIT(TlUlEqualsToSramDw, top_pkg::TL_DW == SramDw)

  // Convert byte mask to SRAM bit mask.
  always_comb begin
    for (int i = 0 ; i < top_pkg::TL_DW/8 ; i++) begin
      wmask_o[8*i+:8] = (tl_i.a_valid) ? {8{tl_i.a_mask[i]}} : '0;
      // only forward valid data here.
      wdata_o[8*i+:8] = (tl_i.a_mask[i] && we_o) ? tl_i.a_data[8*i+:8] : '0;
    end
  end


  // Begin: Request Error Detection

  // wr_attr_error: Check if the request size,mask are permitted.
  //    Basic check of size, mask, addr align is done in tlul_err module.
  //    Here it checks any partial write if ByteAccess isn't allowed.
  assign wr_attr_error = (tl_i.a_opcode == PutFullData || tl_i.a_opcode == PutPartialData) ?
                         (ByteAccess == 0) ? (tl_i.a_mask != '1 || tl_i.a_size != 2'h2) : 1'b0 :
                         1'b0;

  if (ErrOnWrite == 1) begin : gen_no_writes
    assign wr_vld_error = tl_i.a_opcode != Get;
  end else begin : gen_writes_allowed
    assign wr_vld_error = 1'b0;
  end

  if (ErrOnRead == 1) begin: gen_no_reads
    assign rd_vld_error = tl_i.a_opcode == Get;
  end else begin : gen_reads_allowed
    assign rd_vld_error = 1'b0;
  end

  tlul_err u_err (
    .clk_i,
    .rst_ni,
    .tl_i,
    .err_o (tlul_error)
  );

  assign error_internal = wr_attr_error | wr_vld_error | rd_vld_error | tlul_error;
  // End: Request Error Detection

  assign reqfifo_wvalid = a_ack ; // Push to FIFO only when granted
  assign reqfifo_wdata  = '{
    op:     (tl_i.a_opcode != Get) ? OpWrite : OpRead, // To return AccessAck for opcode error
    error:  error_internal,
    size:   tl_i.a_size,
    source: tl_i.a_source
  }; // Store the request only. Doesn't have to store data
  assign reqfifo_rready = d_ack ;

  assign rspfifo_wvalid = rvalid_i & reqfifo_rvalid;
  assign rspfifo_wdata  = '{
    data:  rdata_i,
    error: rerror_i[1]  // Only care for Uncorrectable error
  };
  assign rspfifo_rready = (reqfifo_rdata.op == OpRead & ~reqfifo_rdata.error)
                        ? reqfifo_rready : 1'b0 ;

  // FIFO instance: REQ, RSP

  // ReqFIFO is to store the Access type to match to the Response data.
  //    For instance, SRAM accepts the write request but doesn't return the
  //    acknowledge. In this case, it may be hard to determine when the D
  //    response for the write data should send out if reads/writes are
  //    interleaved. So, to make it in-order (even TL-UL allows out-of-order
  //    responses), storing the request is necessary. And if the read entry
  //    is write op, it is safe to return the response right away. If it is
  //    read reqeust, then D response is waiting until read data arrives.
  prim_fifo_sync #(
    .Width  (ReqFifoWidth),
    .Pass   (1'b0),
  // The oustanding+1 allows the reqfifo to absorb back to back transactions
  // without any wait states.  Alternatively, the depth can be kept as
  // oustanding as long as the outgoing ready is qualified with the acceptance
  // of the response in the same cycle.  Doing so however creates a path from
  // ready_i to ready_o, which may not be desireable.
    .Depth  (Outstanding+1'b1)
  ) u_reqfifo (
    .clk_i,
    .rst_ni,
    .clr_i  (1'b0),
    .wvalid (reqfifo_wvalid),
    .wready (reqfifo_wready),
    .wdata  (reqfifo_wdata),
    .depth  (),
    .rvalid (reqfifo_rvalid),
    .rready (reqfifo_rready),
    .rdata  (reqfifo_rdata)
  );

  // Rationale having #Outstanding depth in response FIFO.
  //    In normal case, if the host or the crossbar accepts the response data,
  //    response FIFO isn't needed. But if in any case it has a chance to be
  //    back pressured, the response FIFO should store the returned data not to
  //    lose the data from the SRAM interface. Remember, SRAM interface doesn't
  //    have back-pressure signal such as read_ready.
  prim_fifo_sync #(
    .Width (RspFifoWidth),
    .Pass  (1'b1),
    .Depth (Outstanding)
  ) u_rspfifo (
    .clk_i,
    .rst_ni,
    .clr_i  (1'b0),
    .wvalid (rspfifo_wvalid),
    .wready (rspfifo_wready),
    .wdata  (rspfifo_wdata),
    .depth  (),
    .rvalid (rspfifo_rvalid),
    .rready (rspfifo_rready),
    .rdata  (rspfifo_rdata)
  );

  // below assertion fails when SRAM rvalid is asserted even though ReqFifo is empty
  `ASSERT(rvalidHighReqFifoEmpty, rvalid_i |-> reqfifo_rvalid)

  // below assertion fails when outstanding value is too small (SRAM rvalid is asserted
  // even though the RspFifo is full)
  `ASSERT(rvalidHighWhenRspFifoFull, rvalid_i |-> rspfifo_wready)

  // If both ErrOnWrite and ErrOnRead are set, this block is useless
  `ASSERT_INIT(adapterNoReadOrWrite, (ErrOnWrite & ErrOnRead) == 0)

  // make sure outputs are defined
  `ASSERT_KNOWN(TlOutKnown_A,    tl_o   )
  `ASSERT_KNOWN(ReqOutKnown_A,   req_o  )
  `ASSERT_KNOWN(WeOutKnown_A,    we_o   )
  `ASSERT_KNOWN(AddrOutKnown_A,  addr_o )
  `ASSERT_KNOWN(WdataOutKnown_A, wdata_o)
  `ASSERT_KNOWN(WmaskOutKnown_A, wmask_o)

endmodule
