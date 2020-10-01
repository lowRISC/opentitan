// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * WLEN (256b) Wide Register File (WDRs)
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 * - Half (WLEN) word write enables
 *
 * This register file is designed to make FPGA synthesis tools infer RAM primitives. For Xilinx
 * FPGA architectures, it will produce RAM32M primitives. Other vendors have not yet been tested.
 */
module otbn_rf_bignum_fpga
  import otbn_pkg::*;
(
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic [WdrAw-1:0] wr_addr_i,
  input  logic [1:0]       wr_en_i,
  input  logic [WLEN-1:0]  wr_data_i,

  input  logic [WdrAw-1:0] rd_addr_a_i,
  output logic [WLEN-1:0]  rd_data_a_o,

  input  logic [WdrAw-1:0] rd_addr_b_i,
  output logic [WLEN-1:0]  rd_data_b_o
);
  logic [WLEN-1:0] rf [NWdr];

  // The reset is not used in this register file version.
  logic unused_rst_ni;
  assign unused_rst_ni = rst_ni;

  // Sync write
  for (genvar i = 0; i < 2; i++) begin : g_rf
    // Split registers into halves for clear separation for the enable terms.
    always_ff @(posedge clk_i) begin
      if (wr_en_i[i] == 1'b1) begin
        rf[wr_addr_i][i*WLEN/2+:WLEN/2] <= wr_data_i[i*WLEN/2+:WLEN/2];
      end
    end
  end

  // Async read
  assign rd_data_a_o = rf[rd_addr_a_i];
  assign rd_data_b_o = rf[rd_addr_b_i];
endmodule
