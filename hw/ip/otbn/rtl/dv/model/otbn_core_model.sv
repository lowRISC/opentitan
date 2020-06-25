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

  input  logic [ImemAddrWidth-1:0] start_addr_i, // start byte address in IMEM

  // Instruction memory (IMEM)
  output logic                     imem_req_o,
  output logic                     imem_write_o,
  output logic [ImemAddrWidth-1:0] imem_addr_o,
  output logic [31:0]              imem_wdata_o,
  input  logic [31:0]              imem_rdata_i,
  input  logic                     imem_rvalid_i,
  input  logic [1:0]               imem_rerror_i,

  // Data memory (DMEM)
  output logic                     dmem_req_o,
  output logic                     dmem_write_o,
  output logic [DmemAddrWidth-1:0] dmem_addr_o,
  output logic [WLEN-1:0]          dmem_wdata_o,
  output logic [WLEN-1:0]          dmem_wmask_o,
  input  logic [WLEN-1:0]          dmem_rdata_i,
  input  logic                     dmem_rvalid_i,
  input  logic [1:0]               dmem_rerror_i
);

  import "DPI-C" context function int run_model(string imem_scope,
                                                int    imem_size,
                                                string dmem_scope,
                                                int    dmem_size);

  localparam ImemSizeWords = ImemSizeByte / 4;
  localparam DmemSizeWords = DmemSizeByte / (WLEN / 8);

  int count;

  always_ff @(posedge clk_i or negedge rst_ni) begin : model_run
    if (!rst_ni) begin
      done_o <= 1'b0;
      count <= -1;
    end else begin
      if (start_i) begin
        count <= run_model(ImemScope, ImemSizeWords, DmemScope, DmemSizeWords);
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
