// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

module spi_fwm_txf_ctrl #(
  parameter int FifoDw = 8,
  parameter int SramAw = 11,
  parameter int SramDw = 32,
  // SramDw should be multiple of FifoDw
  localparam int NumBytes = SramDw/FifoDw, // derived parameter
  localparam int SDW = $clog2(NumBytes),   // derived parameter
  localparam int PtrW = SramAw + SDW + 1   // derived parameter
) (
  input clk_i,
  input rst_ni,

  input spi_device_pkg::spi_mode_e spi_mode_i,

  // Configuration
  input [SramAw-1:0] base_index_i,
  input [SramAw-1:0] limit_index_i,

  input                   abort, // Abort State Machine if TX Async at stuck
  input        [PtrW-1:0] wptr,
  output logic [PtrW-1:0] rptr,
  output logic [PtrW-1:0] depth,

  output logic              fifo_valid,
  input                     fifo_ready,
  output logic [FifoDw-1:0] fifo_wdata,

  output logic              sram_req,
  output logic              sram_write,
  output logic [SramAw-1:0] sram_addr,
  output logic [SramDw-1:0] sram_wdata,
  input                     sram_gnt,
  input                     sram_rvalid,
  input        [SramDw-1:0] sram_rdata,
  input               [1:0] sram_error
);

  logic active;

  logic [SDW-1:0] pos;    // Current write position
  logic [SramAw-1:0] sramf_limit;

  logic [SramDw-1:0] sram_rdata_q;
  logic [SramDw-1:0] fifo_wdata_d;

  logic [PtrW-1:0] wptr_q;


  // State input
  logic sramf_empty;
  logic cnt_eq_end; // pos goes 0 -> 1 -> 2 -> 3 -> then 0

  // State output
  logic sram_req_d;
  logic update_rptr;
  logic latch_wptr;
  logic cnt_rst;  // Reset pos to rptr[SDW-1:0] or 0
  logic cnt_incr;
  logic txf_sel; // 0: sram_rdata, 1: sram_rdata_q


  typedef enum logic [2:0] {
    StIdle   = 'h0,
    StRead   = 'h1,
    StLatch  = 'h2,
    StPush   = 'h3,
    StUpdate = 'h4
  } state_e;

  state_e st_next, st;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st <= StIdle;
    else         st <= st_next;
  end

  assign active = (spi_mode_i == spi_device_pkg::FwMode);

  assign sramf_empty = (rptr == wptr_q);

  assign sramf_limit = limit_index_i - base_index_i;

  // State Machine next , output logic
  always_comb begin
    // default output value
    st_next     = st;
    sram_req_d  = 1'b0;
    update_rptr = 1'b0;
    latch_wptr  = 1'b0;
    fifo_valid  = 1'b0;
    txf_sel     = 1'b0; // 0: sram_rdata, 1:sram_rdata_q
    cnt_rst     = 1'b0; // reset pos to rptr
    cnt_incr    = 1'b0;
    unique case (st)
      StIdle: begin
        latch_wptr = 1'b1;
        if (active && !sramf_empty && fifo_ready) begin
          st_next = StRead;
          sram_req_d = 1'b1;
        end else begin
          st_next = StIdle;
        end
      end

      StRead: begin
        if (sram_gnt) begin
          st_next = StLatch;
          cnt_rst = 1'b1;
          sram_req_d = 1'b0;
        end else begin
          st_next = StRead;
          sram_req_d = 1'b1;
        end
      end

      StLatch: begin
        if (sram_rvalid) begin
          st_next = StPush;
          fifo_valid = 1'b1;
          txf_sel = 1'b0; // select current sram_rdata
          cnt_incr = 1'b1; // increase pos to next byte
        end else begin
          st_next = StLatch;
        end
      end

      StPush: begin
        if (abort) begin
          st_next = StUpdate;
        end else if (!fifo_ready) begin
          st_next = StPush;
        end else if (fifo_ready && !cnt_eq_end) begin
          st_next = StPush;
          fifo_valid = 1'b1;
          txf_sel = 1'b1; // select sram_rdata_q
          cnt_incr = 1'b1;
        end else begin //if (fifo_ready && cnt_eq_end) begin
          // current SRAM word is written to FIFO
          st_next = StUpdate;
        end
      end

      StUpdate: begin
        st_next = StIdle;
        update_rptr = 1'b1;
      end

      default: begin
        st_next = StIdle;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pos <= '0;
    end else if (cnt_rst) begin
      // Reset to rptr to select bytes among fifo_wdata_d
      pos <= rptr[SDW-1:0];
    end else if (cnt_incr) begin
      // Increase position
      pos <= pos + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wptr_q <= '0;
    end else if (latch_wptr) begin
      wptr_q <= wptr;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rptr <= '0;
    end else if (update_rptr) begin
      if (pos == '0) begin
        // full sram word is written.
        if (rptr[PtrW-2:SDW] != sramf_limit) begin
          rptr[PtrW-1:SDW] <= rptr[PtrW-1:SDW] + 1'b1;
          rptr[SDW-1:0] <= '0;
        end else begin
          rptr[PtrW-1] <= ~rptr[PtrW-1];
          rptr[PtrW-2:SDW] <= '0;
          rptr[SDW-1:0]    <= '0;
        end
      end else begin
        // Abort, or partial update (fifo_full), or wptr_q is at the same entry
        rptr[SDW-1:0] <= pos;
      end
    end
  end

  // Depth
  always_comb begin
    if (wptr[PtrW-1] == rptr[PtrW-1]) begin
      // Same phase
      depth = {1'b0, wptr[PtrW-2:0]} - {1'b0, rptr[PtrW-2:0]};
    end else begin
      depth = {1'b0, wptr[PtrW-2:0]}
            + ({1'b0, sramf_limit,{SDW{1'b1}}} - {1'b0, rptr[PtrW-2:0]} + 1'b1);
    end
  end

  assign cnt_eq_end = (wptr_q[PtrW-1:SDW] == rptr[PtrW-1:SDW]) ? wptr_q[SDW-1:0] == pos :
                      pos == '0;


  // Datapath
  assign sram_addr = base_index_i + rptr[PtrW-2:SDW];
  assign sram_write = 1'b0;
  assign sram_wdata = '0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sram_req <= 1'b0;
    else         sram_req <= sram_req_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) sram_rdata_q <= '0;
    else if (sram_rvalid) sram_rdata_q <= sram_rdata;
  end

  assign fifo_wdata_d = (txf_sel) ? sram_rdata_q : sram_rdata ;

  always_comb begin
    fifo_wdata = '0;
    for (int unsigned i = 0 ; i < NumBytes ; i++) begin
      if (pos == i[SDW-1:0]) fifo_wdata = fifo_wdata_d[8*i+:8];
    end
  end

endmodule
