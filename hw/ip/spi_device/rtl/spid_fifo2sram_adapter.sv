// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// FIFO interface to SRAM interface
/*
  This module accepts FIFO interface and converts it into SRAM write
  interface. This module does not have a way to manage the FIFO status
  (empty/ full).
*/

module spid_fifo2sram_adapter #(
  parameter int unsigned FifoWidth = 8,
  parameter int unsigned FifoDepth = 256,

  parameter int unsigned       SramAw = 10,
  parameter int unsigned       SramDw = 32,
  parameter logic [SramAw-1:0] SramBaseAddr = '0,

  parameter bit EnPack = 1, // Byte Write to pack

  localparam int unsigned FifoPtrW = $clog2(FifoDepth)
) (
  input clk_i,
  input rst_ni,

  input                        wvalid_i,
  output logic                 wready_o,
  input        [FifoWidth-1:0] wdata_i,

  output logic [FifoPtrW-1:0] wdepth_o,

  output logic              sram_req_o,
  input                     sram_gnt_i,
  output logic              sram_write_o,
  output logic [SramAw-1:0] sram_addr_o,
  output logic [SramDw-1:0] sram_wdata_o,
  output logic [SramDw-1:0] sram_wmask_o,
  input                     sram_rvalid_i,
  input        [SramDw-1:0] sram_rdata_i,
  input        [1:0]        sram_rerror_i
);

  localparam int unsigned NumEntryPerWord = (EnPack == 1)
                                          ? SramDw/FifoWidth : 1;

  ////////////
  // Signal //
  ////////////
  logic [FifoPtrW-1:0] fifoptr;
  assign wdepth_o = fifoptr;

  logic sram_ack, fifoptr_inc;

  assign sram_req_o = wvalid_i;
  assign wready_o   = sram_gnt_i;

  assign sram_write_o = 1'b 1;

  logic unused_sram_read;
  assign unused_sram_read = ^{sram_rvalid_i, sram_rdata_i, sram_rerror_i};

  if (EnPack == 1 && NumEntryPerWord != 1) begin : g_multiple_entry_per_word
    // If pack, the FifoWidth shall divide SramDw
    `ASSERT_INIT(WidthDivideSramDw_A, SramDw == (SramDw/FifoWidth)*FifoWidth)

    localparam int unsigned SubWordW = $clog2(NumEntryPerWord);

    // Should be multiple of 2
    `ASSERT_INIT(NumEntryPerWordPowerOf2_A, NumEntryPerWord == 2**SubWordW)

    assign sram_addr_o = SramBaseAddr + SramAw'(fifoptr[FifoPtrW-1:SubWordW]);

    always_comb begin
      sram_wdata_o = '0;
      sram_wmask_o = '0;
      for(int unsigned i = 0; i < NumEntryPerWord ; i++) begin
        if (fifoptr[0+:SubWordW] == i) begin
          sram_wdata_o[i*FifoWidth+:FifoWidth] = wdata_i;
          sram_wmask_o[i*FifoWidth+:FifoWidth] = {FifoWidth{1'b1}};
        end
      end
    end

  end else begin : g_one_entry_per_word
    assign sram_addr_o = SramBaseAddr + SramAw'(fifoptr);
    assign sram_wdata_o = SramDw'(wdata_i);
    assign sram_wmask_o = SramDw'(2**FifoWidth-1);
  end

  assign sram_ack = sram_req_o && sram_gnt_i;

  assign fifoptr_inc = sram_ack;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fifoptr <= '0;
    end else if (fifoptr_inc) begin
      fifoptr <= (fifoptr == FifoPtrW'(FifoDepth-1))
               ? '0 : fifoptr + 1'b1;
    end
  end


  ///////////////
  // Assertion //
  ///////////////

  // If fifo ack, sram ack

  // if sram ack, fifo_ptr should increase

  // fifoptr should not exceed Depth


endmodule : spid_fifo2sram_adapter
