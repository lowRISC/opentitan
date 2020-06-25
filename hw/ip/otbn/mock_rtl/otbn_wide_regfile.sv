// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_wide_regfile#(
  parameter int unsigned RegWidth = 256,
  parameter int unsigned RegNum   = 32,
  localparam int Aw               = $clog2(RegNum)
) (
  input logic                 clk_i,
  input logic                 rst_ni,

  input logic [Aw-1:0]        rd_addr_a_i,
  input logic [Aw-1:0]        rd_addr_b_i,

  input logic [Aw-1:0]        wr_addr_i,
  input logic [1:0]           wr_en_i,
  input logic [RegWidth-1:0]  wr_data_i,

  output logic [RegWidth-1:0] rd_data_a_o,
  output logic [RegWidth-1:0] rd_data_b_o
);

  logic [RegWidth-1:0] rf [RegNum];
  logic [1:0]          we_onehot [RegNum];

  for (genvar i = 0;i < RegNum; i++) begin : g_rf
    assign we_onehot[i] = wr_en_i & {2{wr_addr_i == i}};

    // Split registers into halves for clear seperation for the enable terms
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf[i][0+:RegWidth/2] <= '0;
      end else if (we_onehot[i][0]) begin
        rf[i][0+:RegWidth/2] <= wr_data_i[0+:RegWidth/2];
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf[i][RegWidth/2+:RegWidth/2] <= '0;
      end else if (we_onehot[i][1]) begin
        rf[i][RegWidth/2+:RegWidth/2] <= wr_data_i[RegWidth/2+:RegWidth/2];
      end
    end
  end

  assign rd_data_a_o = rf[rd_addr_a_i];
  assign rd_data_b_o = rf[rd_addr_b_i];
endmodule
