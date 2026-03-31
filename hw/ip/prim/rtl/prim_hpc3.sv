// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Description: PINI-secure Hardware Private Circuit (HPC3) / Toffoli Gadget (HPC3o)
//
// This module implements a Probe-Isolating Non-Interference (PINI) secure AND gadget (HPC3) or a
// Toffoli gadget (HPC3o), configured via the compile-time parameter `EnW`. All operands (W, X, Y)
// and the result (Z) are represented as boolean-shared bits in `NumShares` shares.
//
// Compile time configurations:
//   - EnW = 0 (HPC3)  : Computes the masked AND operation:     Z = X & Y
//   - EnW = 1 (HPC3o) : Computes the masked Toffoli operation: Z = W ^ (X & Y)
//
// Pipeline & Timing Requirements:
//   - Randomness: The gadget is fully pipelined and consumes 2 bits of fresh randomness
//     (`r_i` and `rp_i`) per active cycle.
//   - Symmetric Latency: All inputs (x_i, y_i, w_i, r_i, rp_i) share a uniform 1-cycle latency.
//     Unlike HPC2, no input needs to be presented early.
//   - Stall Support: To support stallable pipelines, the `en_i` flip-flop enable signal can be
//     safely deasserted to freeze the internal registers and halt data propagation.
//
// For details, see the following paper:
// Cassiers, Gaetan, et al. "Compress: Generate small and fast masked pipelined circuits."
// available at:
// https://eprint.iacr.org/2023/1600.pdf

module prim_hpc3 #(
  parameter  bit          EnW = 1'b0,
  parameter  bit          PrimFlopEn = 1'b1,
  localparam int unsigned NumShares = 2
) (
  input clk_i,
  input rst_ni,

  // Pipeline stage enable signal.
  input  logic en_i,

  // Masked data inputs.
  input  logic [NumShares-1:0] x_i,
  input  logic [NumShares-1:0] y_i,
  input  logic [NumShares-1:0] w_i,

  // Fresh randomness (two bits per active cycle).
  input  logic r_i,
  input  logic rp_i,

  // Masked data output.
  output logic [NumShares-1:0] z_o
);

  // Stage outputs.
  logic [NumShares-1:0] x_q;
  logic [NumShares-1:0] y_masked_d;
  logic [NumShares-1:0] y_masked_q;
  logic [NumShares-1:0] inner_prod_q;

  // Output-stage combinational nodes.
  logic [NumShares-1:0] xy_masked;    // x[Share] & (y[Share] ^ r)
  logic [NumShares-1:0] inner_prod_d; // ((x[Share] & (y[Share] ^ r)) ^ rp) (^ w_i[Share] if EnW)
  logic [NumShares-1:0] cross_prod;   // x[Share] & (y[OtherShare] ^ r)

  // Stage (en_i): register x, y^r, and the inner product
  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_y_masked
    prim_xor2 u_prim_xor2 (
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
    .en_i  (en_i),
    .d_i   (y_masked_d),
    .q_o   (y_masked_q)
  );

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_x (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en_i),
    .d_i   (x_i),
    .q_o   (x_q)
  );

  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_xy_masked
    prim_and2 u_prim_and2 (
      .in0_i(x_i[Share]),
      .in1_i(y_masked_d[Share]),
      .out_o(xy_masked[Share])
    );
  end

  // HPC3o (EnW=1): XOR w into the inner term before registering.
  // HPC3  (EnW=0): inner term is just (x&y_masked) ^ rp.
  if (EnW) begin : gen_xor_w
    logic [NumShares-1:0] xyw_masked;  // (x[Share] & (y[Share] ^ r)) ^ w[Share]

    for (genvar Share = 0; Share < NumShares; Share++) begin : gen_inner_prod
      prim_xor2 u_prim_xor2_w (
        .in0_i(xy_masked[Share]),
        .in1_i(w_i[Share]),
        .out_o(xyw_masked[Share])
      );

      prim_xor2 u_prim_xor2_d (
        .in0_i(xyw_masked[Share]),
        .in1_i(rp_i),
        .out_o(inner_prod_d[Share])
      );
    end

  end else begin : gen_no_xor_w
    for (genvar Share = 0; Share < NumShares; Share++) begin : gen_inner_prod
      prim_xor2 u_prim_xor2_x_masked (
        .in0_i(xy_masked[Share]),
        .in1_i(rp_i),
        .out_o(inner_prod_d[Share])
      );
    end

    // Consume unused w_i to avoid lint warnings.
    logic unused_w;
    assign unused_w = ^w_i;
  end

  prim_flop_x #(
    .Width(NumShares),
    .ResetValue('0),
    .PrimFlopEn(PrimFlopEn)
  ) u_prim_flop_x_p_inner (
    .clk_i (clk_i),
    .rst_ni(rst_ni),
    .en_i  (en_i),
    .d_i   (inner_prod_d),
    .q_o   (inner_prod_q)
  );

  // Output: cross products use the opposite share's y_masked_q (OtherShare = 1-Share),
  //         then z[Share] = inner_prod_q[Share] ^ cross_prod[Share]
  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_cross_prod
    localparam int OtherShare = (Share == 0) ? 1 : 0;

    prim_and2 u_prim_and2 (
      .in0_i(x_q[Share]),
      .in1_i(y_masked_q[OtherShare]),
      .out_o(cross_prod[Share])
    );
  end

  for (genvar Share = 0; Share < NumShares; Share++) begin : gen_z
    prim_xor2 u_prim_xor2 (
      .in0_i(inner_prod_q[Share]),
      .in1_i(cross_prod[Share]),
      .out_o(z_o[Share])
    );
  end

endmodule : prim_hpc3
