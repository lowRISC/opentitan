// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * ExtWLEN (312b) Wide Register File (WDRs)
 *
 * ExtWLEN allows bits to provide integrity checking to WLEN words on a 32-bit granule. Integrity
 * generation/checking implemented in wrapping otbn_rf_bignum module
 *
 * Features:
 * - 2 read ports
 * - 1 write port
 * - Half (WLEN) word write enables
 */
module otbn_rf_bignum_ff
  import otbn_pkg::*;
#(
  parameter logic [BaseIntgWidth-1:0] WordZeroVal = '0
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic [WdrAw-1:0]   wr_addr_i,
  input  logic [1:0]         wr_en_i,
  input  logic [ExtWLEN-1:0] wr_data_i,

  input  logic [WdrAw-1:0]   rd_addr_a_i,
  output logic [ExtWLEN-1:0] rd_data_a_o,

  input  logic [WdrAw-1:0]   rd_addr_b_i,
  output logic [ExtWLEN-1:0] rd_data_b_o
);
  logic [ExtWLEN-1:0] rf [NWdr];
  logic [1:0]         we_onehot [NWdr];

  for (genvar i = 0; i < NWdr; i++) begin : g_rf
    assign we_onehot[i] = wr_en_i & {2{wr_addr_i == i}};

    // Split registers into halves for clear seperation for the enable terms
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf[i][0+:ExtWLEN/2] <= {BaseWordsPerWLEN/2{WordZeroVal}};
      end else if (we_onehot[i][0]) begin
        rf[i][0+:ExtWLEN/2] <= wr_data_i[0+:ExtWLEN/2];
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf[i][ExtWLEN/2+:ExtWLEN/2] <= {BaseWordsPerWLEN/2{WordZeroVal}};
      end else if (we_onehot[i][1]) begin
        rf[i][ExtWLEN/2+:ExtWLEN/2] <= wr_data_i[ExtWLEN/2+:ExtWLEN/2];
      end
    end
  end

  assign rd_data_a_o = rf[rd_addr_a_i];
  assign rd_data_b_o = rf[rd_addr_b_i];
endmodule
