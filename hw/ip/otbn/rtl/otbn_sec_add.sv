// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Description: First-order masked parallel prefix adder based on HPC3 gadgets.
//
// Implements a masked Sklansky adder operating on two Width-bit Boolean sharings (inp1_i, inp2_i)
// and producing a (Width+1)-bit Boolean sharing (result_o), where the extra bit is the carry out.
// The masking uses 2 shares throughout and is secure against first-order probing attacks. All AND
// gates are implemented with HPC3 or HPC3o gadgets providing glitch-robust PINI security.
//
// Pipeline structure (latency = log2(Width) + 1 cycles, 6 cycles for Width=32):
//   Cycle 0:    Pre-processing: compute generate (g = inp1 & inp2) and propagate (p = inp1 ^ inp2)
//   Cycles 1-5: Prefix tree:    log2(Width) stages of masked generate and propagate operations
//   Cycle 5:    Combinatorial sum generation: result[i] = p_initial[i] ^ g_final[i]
//
// rand_i (RandWidth = 2*(log2(Width)*Width + 1) bits = 322 bits for Width=32) is the random input
// and must be fresh every cycle while data is being processed. Each HPC3 gadget has a dedicated
// 2-bit randomness register loaded from rand_i one cycle before the gadget fires (enabled by
// update_en[level-1]).
//
// valid_i qualifies the inputs. It is registered through the pipeline alongside the data.
// stall_i freezes the entire pipeline (all pipeline registers hold their values).
// valid_o is asserted when a valid result is present at result_o and stall_i is low.
//
// Security verification: verified for first order power SCA using Coco Alma and PROLEAD. Setups
// are under {REPO_TOP}/hw/ip/otbn/pre_sca.

module otbn_sec_add
  import otbn_pkg::*;
#(
  parameter  int Width     = 32,
  localparam int Stages    = $clog2(Width),            // derived parameter
  localparam int RandWidth = 2 * (Stages * Width + 1)  // derived parameter
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  logic                            valid_i,
  input  logic                            stall_i,
  input  logic [RandWidth-1:0]            rand_i,
  input  logic [NumShares-1:0][Width-1:0] inp1_i,
  input  logic [NumShares-1:0][Width-1:0] inp2_i,
  output logic [NumShares-1:0][Width:0]   result_o,
  output logic                            valid_o
);

  // Width needs to be a power of 2.
  `ASSERT_INIT(OtbnSecAddWidthPow2_A, (Width & (Width - 1)) == 0)

  // g[l][s][i]: prefix generate for share s, bit i, after l prefix stages.
  // p[l][s][i]: prefix propagate for share s, bit i, after l prefix stages.
  // pre_p[l][s][i]: initial propagate (inp1^inp2) delayed l pipeline cycles.
  logic [Stages:0][NumShares-1:0][Width-1:0] g;
  logic [Stages:0][NumShares-1:0][Width-1:0] p;
  logic [Stages+1:0][NumShares-1:0][Width-1:0] pre_p;

`ifdef INC_ASSERT
  // Tracks which rand_i bits are consumed by the generate loops below.
  // ASSERT_FINAL at the end of the module verifies full coverage.
  logic [RandWidth-1:0] rand_coverage;
`endif

  // en[l]: valid flag at pipeline stage l.
  // update_en[l]: enable for stage l registers, deasserted during stall.
  logic [Stages+1:0] en;
  logic [Stages:0] update_en;

  assign en[0] = valid_i;

  always_comb begin
    for (int i = 0; i <= Stages; i++) begin
      update_en[i] = en[i] & ~stall_i;
    end
  end

  // Pre-computation stage.
  // pre_p[0] = inp1 ^ inp2
  for (genvar s = 0; s < NumShares; s++) begin : gen_pre_p
    prim_xor2 #(
      .Width(Width)
    ) u_prim_xor2 (
      .in0_i(inp1_i[s]),
      .in1_i(inp2_i[s]),
      .out_o(pre_p[0][s])
    );
  end

  // Align p[0] with g[0], which is delayed by one cycle.
  assign p[0] = pre_p[1];

  // g[0] = inp1 & inp2
  for (genvar i = 0; i < Width; i++) begin : gen_pre_g
    prim_hpc3 #(
      .EnW(1'b0)
    ) u_prim_hpc3_and_g (
      .clk_i,
      .rst_ni,
      .en_i(update_en[0]),
      .x_i ({inp1_i[1][i], inp1_i[0][i]}),
      .y_i ({inp2_i[1][i], inp2_i[0][i]}),
      .w_i ('0),
      .r_i (rand_i[2*i]),
      .rp_i(rand_i[2*i+1]),
      .z_o ({g[0][1][i], g[0][0][i]})
    );

`ifdef INC_ASSERT
    assign rand_coverage[2*i]   = 1'b1;
    assign rand_coverage[2*i+1] = 1'b1;
`endif
  end

  // Prefix Tree Logic.
  //
  // Each level l (1..Stages) is split into Width/(2*Step) groups where Step = 2^(l-1).
  // Each group spans 2*Step bits and is structured into Step feedthrough nodes and Step active
  // nodes [gs, gs+2*Step).
  //  - Feedthrough nodes [gs,      gs+Step):   carry G and P forward unchanged via registers.
  //  - Active nodes      [gs+Step, gs+2*Step): compute updated G and optionally P.
  //    Remote is gs+Step-1, the MSB of the feedthrough half.
  //
  // Exception: active nodes in group 0 (gs==0) compute only G; their P output is never
  // consumed since group 0 bits are never referenced as Remote by any other group.
  //
  // Each G or P computation is realised by one HPC3 gadget and consumes 2 fresh random bits.
  for (genvar level = 1; level <= Stages; level++) begin : gen_prefix_stage
    // Step: half-group size in bits (feedthrough half = lower Step, active half = upper Step).
    localparam int Step = 1 << (level - 1);
    // Absolute rand_i bit offset for this level's gadgets.
    localparam int StageRandOffset = 2 * (level * Width - (Step - 1));

    for (genvar gs = 0; gs < Width; gs = gs + 2*Step) begin : gen_group_logic
      // Remote is the MSB of this group's feedthrough half.
      localparam int Remote = gs + Step - 1;
      // Absolute rand_i bit offset for this group's gadgets.
      // Group 0: G nodes only, 2 bits/node.
      // Others groups: G+P nodes, 4 bits/node.
      localparam int BitsPerNode     = (gs == 0) ? 2 : 4;
      localparam int GroupRandOffset = StageRandOffset + (gs == 0 ? 0 : 2*(gs - Step));

      // Feedthrough nodes: register G and P unchanged into the next level.
      for (genvar i = gs; i < gs + Step; i++) begin : gen_feedthrough
        prim_flop_en #(
          .Width(NumShares),
          .ResetValue('0)
        ) u_prim_flop_en_g (
          .clk_i (clk_i),
          .rst_ni(rst_ni),
          .en_i  (update_en[level]),
          .d_i   ({g[level-1][1][i], g[level-1][0][i]}),
          .q_o   ({g[level][1][i],   g[level][0][i]})
        );

        // For group 0, P is never consumed as a Remote reference, so tie it to zero.
        if (gs > 0) begin : gen_reg_p
          prim_flop_en #(
            .Width(NumShares),
            .ResetValue('0)
          ) u_prim_flop_en_p (
            .clk_i (clk_i),
            .rst_ni(rst_ni),
            .en_i  (update_en[level]),
            .d_i   ({p[level-1][1][i], p[level-1][0][i]}),
            .q_o   ({p[level][1][i],   p[level][0][i]})
          );
        end else begin : gen_no_reg_p
          logic unused_p;
          assign p[level][0][i] = '0;
          assign p[level][1][i] = '0;
          assign unused_p = p[level][0][i] ^ p[level][1][i];
        end
      end

      // Active nodes: compute updated G and optionally P.
      for (genvar i = gs + Step; i < gs + 2 * Step; i++) begin : gen_gadgets
        // Absolute rand_i bit offset for this node's gadgets.
        localparam int NodeRandOffset = GroupRandOffset + BitsPerNode * (i - gs - Step);

        // 2-bit randomness register for the G gadget.
        // Loaded one cycle before the gadget fires.
        logic [1:0] rand_g_q;
        prim_flop_en #(
          .Width(2),
          .ResetValue('0)
        ) u_prim_flop_en_rand_g (
          .clk_i,
          .rst_ni,
          .en_i(update_en[level-1]),
          .d_i (rand_i[NodeRandOffset +: 2]),
          .q_o (rand_g_q)
        );

        // Compute the prefix generate: G[level][i] = G[level-1][i] ^ (P[level-1][i] & G[level-1][Remote])
        prim_hpc3 #(
          .EnW(1'b1)
        ) u_prim_hpc3o_g (
          .clk_i,
          .rst_ni,
          .en_i(update_en[level]),
          .x_i ({g[level-1][1][Remote], g[level-1][0][Remote]}),
          .y_i ({p[level-1][1][i],      p[level-1][0][i]}),
          .w_i ({g[level-1][1][i],      g[level-1][0][i]}),
          .r_i (rand_g_q[0]),
          .rp_i(rand_g_q[1]),
          .z_o ({g[level][1][i], g[level][0][i]})
        );

`ifdef INC_ASSERT
        assign rand_coverage[NodeRandOffset]   = 1'b1;
        assign rand_coverage[NodeRandOffset+1] = 1'b1;
`endif

        // For group 0, P is never consumed as a Remote reference, so tie it to zero.
        if (gs == 0) begin : gen_no_gadget_p
          logic unused_p;
          assign p[level][0][i] = '0;
          assign p[level][1][i] = '0;
          assign unused_p = p[level][0][i] ^ p[level][1][i];

        end else begin : gen_gadget_p
          // 2-bit randomness register for the P gadget.
          logic [1:0] rand_p_q;
          prim_flop_en #(
            .Width(2),
            .ResetValue('0)
          ) u_prim_flop_en_rand_p (
            .clk_i,
            .rst_ni,
            .en_i(update_en[level-1]),
            .d_i (rand_i[NodeRandOffset + 2 +: 2]),
            .q_o (rand_p_q)
          );

          // Compute the prefix propagate: P[level][i] = P[level-1][Remote] & P[level-1][i]
          prim_hpc3 #(
            .EnW(1'b0)
          ) u_prim_hpc3_and_p (
            .clk_i,
            .rst_ni,
            .en_i(update_en[level]),
            .x_i ({p[level-1][1][Remote], p[level-1][0][Remote]}),
            .y_i ({p[level-1][1][i],      p[level-1][0][i]}),
            .w_i ('0),
            .r_i (rand_p_q[0]),
            .rp_i(rand_p_q[1]),
            .z_o ({p[level][1][i], p[level][0][i]})
          );

`ifdef INC_ASSERT
          assign rand_coverage[NodeRandOffset+2] = 1'b1;
          assign rand_coverage[NodeRandOffset+3] = 1'b1;
`endif
        end
      end
    end
  end

  for (genvar level = 1; level <= Stages + 1; level++) begin : gen_feedthrough_stage
    // Feed through pre_p from the pre processing stage for the final sum computation.
    prim_flop_en #(
      .Width(NumShares * Width),
      .ResetValue('0)
    ) u_prim_flop_en_pre_p (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .en_i  (update_en[level-1]),
      .d_i   ({pre_p[level-1][1], pre_p[level-1][0]}),
      .q_o   ({pre_p[level][1],   pre_p[level][0]})
    );

    // Feed through the valid flag signal, which will be used for the stage enable signal.
    prim_flop_en #(
      .Width(1),
      .ResetValue('0)
    ) u_prim_flop_en_enable (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .en_i  (~stall_i),
      .d_i   (en[level-1]),
      .q_o   (en[level])
    );
  end

  // Final Sum Generation: result[i] = p_initial[i] ^ carry_in[i]
  // carry_in[i] = g[Stages][i-1] (prefix generate for bits [0..i-1])
  // carry_in[0] = 0
  for (genvar s = 0; s < NumShares; s++) begin : gen_sum_share
    assign result_o[s][0] = pre_p[Stages+1][s][0];
    for (genvar i = 1; i < Width; i++) begin : gen_sum_bit
      prim_xor2 #(
        .Width(1)
      ) u_prim_xor2 (
        .in0_i(pre_p[Stages+1][s][i]),
        .in1_i(g[Stages][s][i-1]),
        .out_o(result_o[s][i])
      );
    end
    assign result_o[s][Width] = g[Stages][s][Width-1];
  end

  // Output valid signal only when there's no stall.
  assign valid_o = en[Stages+1] && !stall_i;

`ifdef INC_ASSERT
  // Assert that all rand_i bits are assigned.
  `ASSERT_FINAL(OtbnSecAddRandCoverageComplete_A, rand_coverage == {RandWidth{1'b1}})
`endif

endmodule
