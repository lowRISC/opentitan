// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * 32b General Purpose Register File (GPRs)
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 */
module otbn_rf_base_ff
  import otbn_pkg::*;
(
  input logic          clk_i,
  input logic          rst_ni,

  input logic [4:0]    wr_addr_i,
  input logic          wr_en_i,
  input logic [31:0]   wr_data_i,

  input  logic [4:0]   rd_addr_a_i,
  output logic [31:0]  rd_data_a_o,

  input  logic [4:0]   rd_addr_b_i,
  output logic [31:0]  rd_data_b_o
);

  logic [31:0] rf_reg [NGpr];
  logic [31:1] we_onehot;

  // No write-enable for register 0 as writes to it are ignored
  for (genvar i = 1; i < NGpr; i++) begin : g_we_onehot
    assign we_onehot[i] = (wr_addr_i == i) && wr_en_i;
  end

  // No flops for register 0 as it's hard-wired to 0
  assign rf_reg[0] = '0;

  // Generate flops for register 1 - NGpr
  for (genvar i = 1; i < NGpr; i++) begin : g_rf_flops
    logic [31:0] rf_reg_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q <= '0;
      end else if(we_onehot[i]) begin
        rf_reg_q <= wr_data_i;
      end
    end

    assign rf_reg[i] = rf_reg_q;
  end

  assign rd_data_a_o = rf_reg[rd_addr_a_i];
  assign rd_data_b_o = rf_reg[rd_addr_b_i];
endmodule
