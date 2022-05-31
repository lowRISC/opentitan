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
 *
 * Register 0 is fixed to 0.
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 */
module otbn_rf_base_fpga
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
  logic                    wr_en;

  // The reset is not used in this register file version.
  logic unused_rst_ni;
  assign unused_rst_ni = rst_ni;

  // No write-enable for register 0 as writes to it are ignored.
  assign wr_en = (wr_addr_i == '0) ? 1'b0 : wr_en_i;

  // Sync write
  // Note that the SystemVerilog LRM requires variables on the LHS of assignments within
  // "always_ff" to not be written to by any other process. However, to enable the initialization
  // of the inferred RAM32M primitives with non-zero values, below "initial" procedure is needed.
  // Therefore, we use "always" instead of the generally preferred "always_ff" for the synchronous
  // write procedure.
  always @(posedge clk_i) begin : g_rf_reg
    if (wr_en == 1'b1) begin
      rf_reg[wr_addr_i] <= wr_data_i;
    end
  end

  // Make sure we initialize the BRAM with the correct register reset value.
  initial begin
    for (int k = 0; k < NGpr; k++) begin
      rf_reg[k] = WordZeroVal;
    end
  end

  // Async read
  assign rd_data_a_o = (rd_addr_a_i == '0) ? WordZeroVal : rf_reg[rd_addr_a_i];
  assign rd_data_b_o = (rd_addr_b_i == '0) ? WordZeroVal : rf_reg[rd_addr_b_i];

  // SEC_CM: RF_BASE.DATA_REG_SW.GLITCH_DETECT
  // This checks for spurious WE strobes on the regfile.
  // Since the FPGA uses a memory macro, there is only one write-enable strobe to check.
  logic we_err;
  assign we_err = wr_en && !wr_en_i;

  // We need to register this to avoid timing loops.
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_err
    if (!rst_ni) begin
      we_err_o <= '0;
    end else begin
      we_err_o <= we_err;
    end
  end

endmodule
