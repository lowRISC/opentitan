// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * 39b General Purpose Register File (GPRs)
 *
 * 39b to support 32b register with 7b integrity. Integrity generation/checking implemented in
 * wrapping otbn_rf_base module
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 */
module otbn_rf_base_ff
  import otbn_pkg::*;
#(
  parameter logic [BaseIntgWidth-1:0] WordZeroVal = '0
) (
  input logic                     clk_i,
  input logic                     rst_ni,

  input logic  [4:0]               wr_addr_i,
  input logic                      wr_en_i,
  input logic  [BaseIntgWidth-1:0] wr_data_i,

  input  logic [4:0]               rd_addr_a_i,
  output logic [BaseIntgWidth-1:0] rd_data_a_o,

  input  logic [4:0]               rd_addr_b_i,
  output logic [BaseIntgWidth-1:0] rd_data_b_o,

  // Indicates whether a spurious WE has been seen in the last cycle.
  output logic                     we_err_o
);

  logic [BaseIntgWidth-1:0] rf_reg [NGpr];
  logic [31:0] we_onehot;

  for (genvar i = 0; i < NGpr; i++) begin : g_we_onehot
    assign we_onehot[i] = (wr_addr_i == i) && wr_en_i;
  end

  // No flops for register 0 as it's hard-wired to 0
  assign rf_reg[0] = WordZeroVal;

  // No flops for register 1 as it's call stack and handled in a different module.
  assign rf_reg[1] = WordZeroVal;

  // Generate flops for register 1 - NGpr
  for (genvar i = 2; i < NGpr; i++) begin : g_rf_flops
    logic [BaseIntgWidth-1:0] rf_reg_q;

    always_ff @(posedge clk_i) begin
      if(we_onehot[i]) begin
        rf_reg_q <= wr_data_i;
      end
    end

    assign rf_reg[i] = rf_reg_q;
  end

  assign rd_data_a_o = rf_reg[rd_addr_a_i];
  assign rd_data_b_o = rf_reg[rd_addr_b_i];

  // Buffer the decoded write enable bits so that the checker
  // is not optimized into the address decoding logic.
  logic [31:0] we_onehot_buf;
  prim_buf #(
    .Width(32)
  ) u_prim_buf (
    .in_i(we_onehot),
    .out_o(we_onehot_buf)
  );

  // SEC_CM: RF_BASE.DATA_REG_SW.GLITCH_DETECT
  // This checks for spurious WE strobes on the regfile.
  logic we_err;
  prim_onehot_check #(
    .AddrWidth(5),
    .AddrCheck(1),
    .EnableCheck(1)
  ) u_prim_onehot_check (
    .clk_i,
    .rst_ni,
    .oh_i(we_onehot_buf),
    .addr_i(wr_addr_i),
    .en_i(wr_en_i),
    .err_o(we_err)
  );

  // We need to register this to avoid timing loops.
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_err
    if (!rst_ni) begin
      we_err_o <= '0;
    end else begin
      we_err_o <= we_err;
    end
  end

endmodule
