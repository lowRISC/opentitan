// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OpenTitan Big Number Accelerator (OTBN) Core
 *
 * This module is the top-level of the OTBN processing core.
 */
module otbn_core_model
  import otbn_pkg::*;
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = 4096,

  // Scope of the instruction memory (for DPI)
  parameter string ImemScope = "",
  // Scope of the data memory (for DPI)
  parameter string DmemScope = "",

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte),
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte)
)(
  input  logic  clk_i,
  input  logic  rst_ni,

  input  logic  start_i, // start the operation
  output logic  done_o,  // operation done

  input  logic [ImemAddrWidth-1:0] start_addr_i // start byte address in IMEM
);

  import "DPI-C" context function int run_model(string imem_scope,
                                                int    imem_size,
                                                string dmem_scope,
                                                int    dmem_size,
                                                int    start_addr);

  localparam ImemSizeWords = ImemSizeByte / 4;
  localparam DmemSizeWords = DmemSizeByte / (WLEN / 8);

  int count;

  `ASSERT_INIT(StartAddr32_A, ImemAddrWidth <= 32);
  logic [31:0] start_addr_32;
  assign start_addr_32 = {{32 - ImemAddrWidth{1'b0}}, start_addr_i};

  always_ff @(posedge clk_i or negedge rst_ni) begin : model_run
    if (!rst_ni) begin
      done_o <= 1'b0;
      count <= -1;
    end else begin
      if (start_i) begin
        count <= run_model(ImemScope, ImemSizeWords, DmemScope, DmemSizeWords, start_addr_32);
        done_o <= 1'b0;
      end else begin
        if (count == 0) begin
          done_o <= 1'b1;
          count <= -1;
        end else begin
          done_o <= 1'b0;
          count <= count - 1;
        end
      end
    end
  end

endmodule
