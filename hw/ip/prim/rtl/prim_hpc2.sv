// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Description: PINI-secure Hardware Private Circuit (HPC2) / Toffoli Gadget (HPC2o)
//
// This module implements a Probe-Isolating Non-Interference (PINI) secure AND gadget (HPC2) or a
// Toffoli gadget (HPC2o), configured via the compile-time parameter `EnW`. All operands (W, X, Y)
// and the result (Z) are represented as boolean-shared bits in `NumShares` shares.
//
// Compile time configurations:
//   - EnW = 0 (HPC2)  : Computes the masked AND operation:     Z = X & Y
//   - EnW = 1 (HPC2o) : Computes the masked Toffoli operation: Z = W ^ (X & Y)
//
// Pipeline & Timing Requirements:
//   - Randomness: The gadget is fully pipelined and consumes 1 bit of fresh randomness (`r_i`) per
//     active cycle.
//   - Asymmetric Latency: Due to internal staging, `y_i` and `r_i` have a 2-cycle latency, whereas
//     `x_i` and `w_i` have a 1-cycle latency. Consequently, `y_i` and `r_i` must be driven at
//      least one cycle prior to their corresponding `x_i` and `w_i` inputs.
//   - Stall Support: To support stallable pipelines, the `en1_i` and `en2_i` flip-flop enable
//     signals can be safely deasserted to freeze the internal registers and halt data propagation.
//
// For details, see the following paper:
// Cassiers, Gaetan, et al. "Compress: Generate small and fast masked pipelined circuits."
// available at:
// https://eprint.iacr.org/2023/1600.pdf

module prim_hpc2 #(
  parameter  bit          EnW = 1'b0,
  parameter  bit          PrimFlopEn = 1'b1,
  localparam int unsigned NumShares = 2
) (
  input clk_i,
  input rst_ni,

  // Pipeline stage enable signals.
  input  logic en1_i,
  input  logic en2_i,

  // Masked data inputs.
  input  logic [NumShares-1:0] x_i,
  input  logic [NumShares-1:0] y_i,
  input  logic [NumShares-1:0] w_i,

  // Randomness input.
  input  logic r_i,

  // Masked data output.
  output logic [NumShares-1:0] z_o
);

  // Stage 1 outputs.
  logic                 r_q;
  logic [NumShares-1:0] y_q;
  logic [NumShares-1:0] y_masked_d;
  logic [NumShares-1:0] y_masked_q;

  // Stage 2 combinational nodes.
  logic [NumShares-1:0] x_inv;
  logic [NumShares-1:0] xy;            // x[Share] & y_q[Share]
  logic [NumShares-1:0] x_inv_r_d;     // ~x[Share] & r_q
  logic [NumShares-1:0] cross_prod_d;  // x[Share] & y_masked_q[OtherShare]
  logic [NumShares-1:0] inner_prod_d;  // xy[Share] (^ w_i[Share] if EnW)

  // Stage 2 outputs.
  logic [NumShares-1:0] x_inv_r_q;
  logic [NumShares-1:0] inner_prod_q;
  logic [NumShares-1:0] cross_prod_q;
  logic [NumShares-1:0] merge_cross;

  // Stage 1: Register y, y^r, and r.
  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_y_masked
    prim_xor2 #(
      .Width(1)
    ) u_prim_xor2 (
      .in0_i(y_i[Share]),
      .in1_i(r_i),
      .out_o(y_masked_d[Share])
    );
  end

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_y_masked (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en1_i),
    .d_i   (y_masked_d),
    .q_o   (y_masked_q)
  );

  prim_flop_x #(
    .Width(1),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_r (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en1_i),
    .d_i   (r_i),
    .q_o   (r_q)
  );

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_y (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en1_i),
    .d_i   (y_i),
    .q_o   (y_q)
  );

  // Stage 2: Compute xy_masked, x_inv_r, and cross products.
  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_xy_masked
    prim_and2 u_prim_and2 (
      .in0_i(x_i[Share]),
      .in1_i(y_q[Share]),
      .out_o(xy[Share])
    );

    prim_inv u_prim_inv (
      .in_i (x_i[Share]),
      .out_o(x_inv[Share])
    );

    prim_and2 u_prim_and2_x_masked (
      .in0_i(x_inv[Share]),
      .in1_i(r_q),
      .out_o(x_inv_r_d[Share])
    );
  end

  // Cross products use the opposite share's y_masked_q (OtherShare = ~Share).
  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_cross_prod
    localparam int OtherShare = (Share == 0) ? 1 : 0;

    prim_and2 u_prim_and2 (
      .in0_i(x_i[Share]),
      .in1_i(y_masked_q[OtherShare]),
      .out_o(cross_prod_d[Share])
    );
  end

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_x_inv_r (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en2_i),
    .d_i   (x_inv_r_d),
    .q_o   (x_inv_r_q)
  );

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_cross_prod (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en2_i),
    .d_i   (cross_prod_d),
    .q_o   (cross_prod_q)
  );

  // HPC2o (EnW=1): XOR w and xy_masked into the inner term before registering.
  // HPC2  (EnW=0): register the inner term and xy_masked separately, XOR after.
  if (EnW) begin : gen_xor_w
    for (genvar Share = 0; Share < NumShares; Share++) begin : gen_inner_prod
      prim_xor2 u_prim_xor2_w (
        .in0_i(xy[Share]),
        .in1_i(w_i[Share]),
        .out_o(inner_prod_d[Share])
      );
    end

  end else begin : gen_no_xor_w
    for (genvar Share = 0; Share < NumShares; Share++) begin : gen_inner_prod
      assign inner_prod_d[Share] = xy[Share];
    end

    // Consume unused w_i to avoid lint warnings.
    logic unused_w;
    assign unused_w = ^w_i;
  end

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_inner_prod (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en2_i),
    .d_i   (inner_prod_d),
    .q_o   (inner_prod_q)
  );

  // Output: z[Share] = inner_prod_q[Share] ^ cross_prod_q[Share]
  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_z
    prim_xor2 u_prim_xor2_merge_cross (
      .in0_i(cross_prod_q[Share]),
      .in1_i(x_inv_r_q[Share]),
      .out_o(merge_cross[Share])
    );

    prim_xor2 u_prim_xor2_output (
      .in0_i(merge_cross[Share]),
      .in1_i(inner_prod_q[Share]),
      .out_o(z_o[Share])
    );
  end

  // Asymmetric latency: en1_i (y_i/r_i path) must have fired at least once
  // before en2_i (x_i/w_i path) fires. Stalls are allowed between the two.
  // Stage 1 must not be overwritten while its data is still pending in Stage 2.
`ifndef SYNTHESIS
  logic s_stage1_pending;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) s_stage1_pending <= 1'b0;
    else         s_stage1_pending <= en1_i || (s_stage1_pending && !en2_i);
  end

  // Stage 2 may only fire if Stage 1 has been triggered since the last Stage 2.
  `ASSERT(AsymLatencyEn1BeforeEn2, en2_i |-> s_stage1_pending, clk_i, !rst_ni)
  // Stage 1 may not overwrite pending data unless Stage 2 is completing this cycle.
  `ASSERT(AsymLatencyNoStage1Overwrite,
      en1_i && s_stage1_pending |-> en2_i, clk_i, !rst_ni)
`endif

endmodule : prim_hpc2
