// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * 32b General Purpose Register File (GPRs)
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 *
 * Register 0 is fixed to 0.
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 */
module otbn_rf_base_fpga
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
  logic        wr_en;

  // The reset is not used in this register file version.
  logic unused_rst_ni;
  assign unused_rst_ni = rst_ni;

  // No write-enable for register 0 as writes to it are ignored.
  assign wr_en = (wr_addr_i == '0) ? 1'b0 : wr_en_i;

  // Sync write
  always_ff @(posedge clk_i) begin : g_rf_reg
    if (wr_en == 1'b1) begin
      rf_reg[wr_addr_i] <= wr_data_i;
    end
  end

  // Async read
  assign rd_data_a_o = (rd_addr_a_i == '0) ? '0 : rf_reg[rd_addr_a_i];
  assign rd_data_b_o = (rd_addr_b_i == '0) ? '0 : rf_reg[rd_addr_b_i];
endmodule
