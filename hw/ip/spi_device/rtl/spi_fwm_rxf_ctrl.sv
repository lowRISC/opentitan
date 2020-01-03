// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

module spi_fwm_rxf_ctrl #(
  parameter int unsigned FifoDw = 8,
  parameter int unsigned SramAw = 11,
  parameter int unsigned SramDw = 32,
  // Do not touch below
  // SramDw should be multiple of FifoDw
  localparam int unsigned NumBytes = SramDw/FifoDw,    // derived parameter
  localparam int unsigned SDW      = $clog2(NumBytes), // derived parameter
  localparam int unsigned PtrW     = SramAw + SDW + 1  // derived parameter
) (
  input clk_i,
  input rst_ni,

  // Configuration
  input      [SramAw-1:0] base_index_i,
  input      [SramAw-1:0] limit_index_i,
  input             [7:0] timer_v,
  input        [PtrW-1:0] rptr,
  output logic [PtrW-1:0] wptr,
  output logic [PtrW-1:0] depth,

  output logic            full,

  input               fifo_valid,
  output logic        fifo_ready,
  input  [FifoDw-1:0] fifo_rdata,

  output logic              sram_req,
  output logic              sram_write,
  output logic [SramAw-1:0] sram_addr,
  output logic [SramDw-1:0] sram_wdata,
  input                     sram_gnt,
  input                     sram_rvalid,
  input        [SramDw-1:0] sram_rdata,
  input               [1:0] sram_error
);

  // Internal variable
  logic [NumBytes-1:0] byte_enable;
  logic [SDW-1:0]      pos;   // current byte position
  logic [7:0] cur_timer;
  logic [SramAw-1:0] sramf_limit;

  // State input
  logic sramf_full;   // SRAM Fifo full
  logic full_sramwidth;   // Write data filled full SRAM
  logic timer_expired;

  // State output
  logic update_wdata;
  logic clr_byte_enable;
  logic sram_req_d;
  logic sram_write_d;
  logic sram_wdata_sel;
  logic timer_rst;
  logic update_wptr;

  typedef enum logic [2:0] {
    StIdle   = 'h0,
    StPop    = 'h1,
    StWait   = 'h2,
    StRead   = 'h3,
    StModify = 'h4,
    StWrite  = 'h5,
    StUpdate = 'h6
  } state_e;

  state_e st_next, st;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st <= StIdle;
    else         st <= st_next;
  end


  logic [PtrW-1:0] ptr_cmp;
  assign ptr_cmp = rptr ^ wptr;
  // TODO: Check partial SRAM width read condition
  assign sramf_full = (ptr_cmp[PtrW-1] == 1'b1) && (ptr_cmp[PtrW-2:SDW] == '0);
  assign full = sramf_full;

  assign sramf_limit = limit_index_i - base_index_i;

  // Write pointer update
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wptr <= '0;
    end else if (update_wptr) begin
      if (byte_enable == '0) begin
        // as byte enable is cleared, it means full write was done
        if (wptr[PtrW-2:SDW] == sramf_limit) begin
          wptr[PtrW-1] <= ~wptr[PtrW-1];
          wptr[PtrW-2:0] <= '0;
        end else begin
          wptr[PtrW-2:SDW] <= wptr[PtrW-2:SDW] + 1'b1;
          wptr[SDW-1:0] <= '0;
        end
      end else begin
        wptr[SDW-1:0] <= pos;
      end
    end
  end

  // Full check
  assign full_sramwidth = (1'b1 == &byte_enable);

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

  //timer
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cur_timer <= '1;
    end else if (timer_rst) begin
      cur_timer <= timer_v;
    end else if (st == StWait) begin
      if (cur_timer != '0) cur_timer <= cur_timer - 1'b1;
    end
  end
  assign timer_expired = (cur_timer == '0);

  // Data output
  assign sram_addr = base_index_i + wptr[PtrW-2:SDW];

  // Byte Enable control
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      byte_enable <= '0;
      pos <= '0;
    end else if (update_wdata) begin
      byte_enable[pos] <= 1'b1;
      if (pos == SDW'(NumBytes-1)) pos <= '0;
      else                         pos <= pos + 1'b1;
    end else if (clr_byte_enable) begin
      byte_enable <= '0;
      pos <= '0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sram_wdata <= '0;
    end else if (update_wdata) begin
      sram_wdata[8*pos+:8] <= fifo_rdata;
    end else if (sram_wdata_sel == 1'b1) begin
      for (int i = 0 ; i < NumBytes ; i++) begin
        if (!byte_enable[i]) begin
          sram_wdata[8*i+:8] <= sram_rdata[8*i+:8];
        end
      end
    end
  end

  `COVER(partialWriteCover, st == StModify, clk_i, !rst_ni)

  // If FIFO is not empty, initiate SRAM write.
  // As FIFOWidth and SRAM Width are different, RMW is required.
  // If host writes always DWord size, it is easy but it is not guaranteed.
  //

  // Next State & output logic
  always_comb begin
    fifo_ready = 1'b0;
    update_wdata = 1'b0;
    clr_byte_enable = 1'b0;
    sram_req_d = 1'b0;
    sram_write_d = 1'b0;
    sram_wdata_sel = 1'b0;
    timer_rst = 1'b0;
    update_wptr = 1'b0;

    unique case (st)
      StIdle: begin
        // Out of reset state. If SRAM Fifo is not full and RX Fifo is not empty,
        // state machine starts process incoming data
        if (fifo_valid && !sramf_full) begin
          st_next = StPop;
          fifo_ready = 1'b1;
          update_wdata = 1'b1;
        end else begin
          st_next = StIdle;
        end
      end

      StPop: begin
        // Pop entries from FIFO. It moves to WAIT if Fifo is empty and still not
        // filled up full sram data width. If anytime while popping the entries
        // and full sram data width is filled, it directly moves to Write state
        if (fifo_valid && !full_sramwidth) begin
          st_next = StPop;
          fifo_ready = 1'b1;
          update_wdata = 1'b1;
        end else if (full_sramwidth) begin
          st_next = StWrite;
          clr_byte_enable = 1'b1;
          sram_req_d   = 1'b1;
          sram_write_d = 1'b1;
        end else begin
          st_next = StWait;
          timer_rst = 1'b1;
        end
      end

      StWait: begin
        // Wait up to X clocks. This state is useful to reduce traffic to SRAM.
        // State machine gathers up to SramDw then tries to write at once.
        // If not, it needs to Read-Modify-Write for every byte
        if (fifo_valid) begin
          st_next = StPop;
          fifo_ready = 1'b1;
          update_wdata = 1'b1;
        end else if (!fifo_valid && timer_expired) begin
          st_next = StRead;
          sram_req_d   = 1'b1;
          sram_write_d = 1'b0;
        end else begin
          st_next = StWait;
        end
      end

      StRead: begin
        // As counter expires, RMW is only option. State machine reads from current
        // write pointer address (chopping lower bits).
        if (sram_gnt) begin
          st_next = StModify;
        end else begin
          st_next = StRead;
          sram_req_d   = 1'b1;
          sram_write_d = 1'b0;
        end
      end

      StModify: begin
        // Waits until read data arrives.
        if (sram_rvalid) begin
          st_next = StWrite;
          sram_req_d   = 1'b1;
          sram_write_d = 1'b1;
          sram_wdata_sel = 1'b1;
        end else begin
          st_next = StModify;
        end
      end

      StWrite: begin
        // Regardless of RMW or just full Words write, statemachine writes data
        // into SRAM Fifo
        if (sram_gnt) begin
          st_next = StUpdate;
        end else begin
          st_next = StWrite;
          sram_req_d   = 1'b1;
          sram_write_d = 1'b1;
        end
      end

      StUpdate: begin
        // Now, update write pointer then goes back to StIdle.
        // It can goes to StPop state directly but doesn't have to as SPI is slower
        st_next = StIdle;
        update_wptr = 1'b1;
      end

      default: begin
        st_next = StIdle;
      end
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sram_req <= 1'b0;
      sram_write <= 1'b0;
    end else begin
      sram_req <= sram_req_d;
      sram_write <= sram_write_d;
    end
  end

endmodule
