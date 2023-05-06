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


always_ff @(posedge clk_gp[0] or negedge rst_ni) begin
  if (!rst_ni) begin
    intq[0] <= 1'b0;
  end else begin
    intq[0] <= stage_d[0];
  end
end

always_ff @(negedge clk_gp[0] or negedge rst_ni) begin
  if (!rst_ni) begin
    stage_q[0] <= 1'b0;
  end else begin
    stage_q[0] <= intq[0];
  end
end

tc_clk_gating #(     
) u_cg_0 (
  .clk_i(clk_gp[0]),
  .en_i(stage_q[0]),
  .test_en_i(1'b0),
  .clk_o(clk_glitch_off[0])
);

always_ff @(posedge clk_gp[1] or negedge rst_ni) begin
  if (!rst_ni) begin
    intq[1] <= 1'b0;
  end else begin
    intq[1] <= stage_d[1];
  end
end

always_ff @(negedge clk_gp[1] or negedge rst_ni) begin
  if (!rst_ni) begin
    stage_q[1] <= 1'b0;
  end else begin
    stage_q[1] <= intq[1];
  end
end

tc_clk_gating #(     
) u_cg_1 (
  .clk_i(clk_gp[1]),
  .en_i(stage_q[1]),
  .test_en_i(1'b0),
  .clk_o(clk_glitch_off[1])
);

assign clk_o = |clk_glitch_off;

endmodule
