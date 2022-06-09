// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Glitch free clock mux using parallel two flop synchronizers

module prim_clock_gp_mux2 #(
  parameter bit NoFpgaBufG = 1'b0,
  parameter bit FpgaBufGlobal = 1,
  parameter bit GlitchProtect = 1
) (
  input        clk0_i,
  input        clk1_i,
  input        sel_i,
  input        rst_ni,
  input        test_en_i,
  output logic clk_o
);

logic [1:0] clk_gp;
logic [1:0] intq;
logic [1:0] stage_d;
logic [1:0] stage_q;
logic [1:0] clk_glitch_off;

assign clk_gp = {clk1_i, clk0_i};
assign stage_d = {sel_i & !stage_q[0], !sel_i & !stage_q[1]};

generate
  genvar i;
  for (i = 0; i < 2; i = i++) begin: gen_two_flops
    always_ff @(posedge clk_gp[i] or negedge rst_ni) begin: stage1
      if (!rst_ni) begin
        intq[i] <= 1'b0;
      end else begin
        intq[i] <= stage_d[i];
      end
    end

    always_ff @(negedge clk_gp[i] or negedge rst_ni) begin: stage2
      if (!rst_ni) begin
        stage_q[i] <= 1'b0;
      end else begin
        stage_q[i] <= intq[i];
      end
    end

    prim_clock_gating #(
      .FpgaBufGlobal(FpgaBufGlobal)
    ) u_cg (
      .clk_i(clk_gp[i]),
      .en_i(stage_q[i]),
      .test_en_i(1'b0),
      .clk_o(clk_glitch_off[i])
    );

  end
endgenerate

assign clk_o = |clk_glitch_off;

endmodule
