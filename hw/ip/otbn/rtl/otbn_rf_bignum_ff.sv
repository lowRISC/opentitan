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
  output logic [ExtWLEN-1:0] rd_data_b_o,

  input  rf_predec_bignum_t rf_predec_bignum_i
);
  logic [ExtWLEN-1:0] rf [NWdr];
  logic [1:0]         we_onehot [NWdr];

  logic unused_addr;

  for (genvar i = 0; i < NWdr; i++) begin : g_rf
    logic [ExtWLEN-1:0] wr_data_blanked;
    assign we_onehot[i] = wr_en_i & {2{wr_addr_i == i}};

    // SEC_CM: DATA_REG_SW.SCA
    prim_blanker #(.Width(ExtWLEN)) u_wdata_blanker(
      .in_i (wr_data_i),
      .en_i (rf_predec_bignum_i.rf_we[i]),
      .out_o(wr_data_blanked)
    );

    // Split registers into halves for clear seperation for the enable terms
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf[i][0+:ExtWLEN/2] <= {BaseWordsPerWLEN/2{WordZeroVal}};
      end else if (rf_predec_bignum_i.rf_we[i] & we_onehot[i][0]) begin
        rf[i][0+:ExtWLEN/2] <= wr_data_blanked[0+:ExtWLEN/2];
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf[i][ExtWLEN/2+:ExtWLEN/2] <= {BaseWordsPerWLEN/2{WordZeroVal}};
      end else if (rf_predec_bignum_i.rf_we[i] & we_onehot[i][1]) begin
        rf[i][ExtWLEN/2+:ExtWLEN/2] <= wr_data_blanked[ExtWLEN/2+:ExtWLEN/2];
      end
    end
  end

  // SEC_CM: DATA_REG_SW.SCA
  prim_onehot_mux #(
    .Width(ExtWLEN),
    .Inputs(NWdr)
  ) u_rd_mux_a (
    .clk_i,
    .rst_ni,
    .in_i  (rf),
    .sel_i (rf_predec_bignum_i.rf_ren_a),
    .out_o (rd_data_a_o)
  );

  prim_onehot_mux  #(
    .Width(ExtWLEN),
    .Inputs(NWdr)
  ) u_rd_mux_b (
    .clk_i,
    .rst_ni,
    .in_i  (rf),
    .sel_i (rf_predec_bignum_i.rf_ren_b),
    .out_o (rd_data_b_o)
  );

  assign unused_addr = ^rd_addr_a_i ^ ^rd_addr_b_i ^ ^wr_addr_i;
endmodule
