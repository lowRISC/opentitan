// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Dummy placeholder module for a Valid-Hold register file supporting same-cycle reads of name and
// version registers.

module vh_regs
  import tlul_pkg::*;
#(
  parameter bit [31:0] VH_NAME_0    = 32'hDEADBEEF,
  parameter bit [31:0] VH_NAME_1    = 32'hCAFEBABE,
  parameter bit [31:0] VH_VERSION_0 = 32'h00000001,
  parameter bit [31:0] VH_VERSION_1 = 32'h00000000,

  parameter int ADDR_WIDTH = top_pkg::TL_AW,
  parameter int DATA_WIDTH = top_pkg::TL_DW,
  parameter int MASK_WIDTH = DATA_WIDTH >> 3,
  parameter int USER_WIDTH = 32,
  parameter int ID_WIDTH   = top_pkg::TL_AIW
) (
  input clk_i,
  input rst_ni,

  input  logic                  dv_i,
  output logic                  hld_o,
  input  logic [ADDR_WIDTH-1:0] addr_i,
  input  logic                  write_i,
  input  logic [DATA_WIDTH-1:0] wdata_i,
  input  logic [MASK_WIDTH-1:0] wstrb_i,
  input  logic [2:0]            size_i,
  output logic [DATA_WIDTH-1:0] rdata_o,
  output logic                  error_o,
  // Optional signals
  input  logic                  last_i,
  input  logic [USER_WIDTH-1:0] user_i,
  input  logic [ID_WIDTH-1:0]   id_i
);

  always_comb begin
    rdata_o = '0;
    if (dv_i) begin
      unique case (addr_i[3:0])
        4'h0:    rdata_o = VH_NAME_0;
        4'h4:    rdata_o = VH_NAME_1;
        4'h8:    rdata_o = VH_VERSION_0;
        4'hc:    rdata_o = VH_VERSION_1;
        default: rdata_o = '0;
      endcase
    end
  end

  assign hld_o   = 1'b0;
  assign error_o = 1'b0;

  logic unused_signals;
  assign unused_signals = ^{clk_i, rst_ni, addr_i[31:4], write_i, wdata_i, wstrb_i, size_i, last_i,
    user_i, id_i};

endmodule
