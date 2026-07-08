// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// First-order masked operation accelerator for the OTBN cryptographic coprocessor.
//
// Implements four masked operations on shared SecAddWidth-bit inputs, all backed by the HPC3-based
// masked parallel prefix adder (otbn_sec_add / otbn_sec_add_mod). All operations are secure
// against first-order power side-channel attacks under the transition- and glitch-extended probing
// model.
//
// Supported operations (selected by mask_op_i):
//
//   SecAdd:
//     Masked addition, no modular reduction.
//     in0_i is a Boolean sharing (a0, a1) where a = a0 XOR a1.
//     in1_i is a Boolean sharing (b0, b1) where b = b0 XOR b1.
//     result_o is a Boolean sharing (c0, c1) where c = c0 XOR c1 = (a + b) mod 2^SecAddWidth.
//     The computation involves a single pass through otbn_sec_add_mod with adder_enable_mod=0.
//
//   SecAddMod:
//     Masked modular addition. Let inp1, inp2 be the true operands (inp1 + inp2 < mod_i).
//     in0_i is a Boolean sharing (a0, a1) where a = a0 XOR a1.
//     in1_i is a Boolean sharing (b0, b1) where b = b0 XOR b1.
//     The caller must pre-encode inputs so that a + b = inp1 + inp2 + (2^SecAddWidth - mod_i),
//     i.e. the two's-complement negation of mod_i is absorbed into the combined XOR-sums.
//     result_o is a Boolean sharing (c0, c1) where c = c0 XOR c1 = (inp1 + inp2) mod mod_i.
//
//   ArithToBool (A2B):
//     Arithmetic-to-Boolean share conversion modulo mod_i.
//     in0_i is an arithmetic sharing (a0, a1) where a = a0 + a1 mod mod_i.
//     result_o is a Boolean sharing (b0, b1) where b = b0 XOR b1 = a.
//
//     Before being fed into otbn_sec_add_mod, the arithmetic shares are re-masked with
//     remask_rand_i (r0, r1) and shifted by mod_neg:
//       adder_inp1 = (a0 XOR r0,             r0)
//       adder_inp2 = ((a1 + mod_neg) XOR r1, r1)
//     where mod_neg = 2^SecAddWidth - mod_i. Their sum a0 + a1 + mod_neg = a + mod_neg feeds
//     otbn_sec_add_mod, whose two-pass computation yields a Boolean sharing of a.
//
//   BoolToArith (B2A):
//     Boolean-to-Arithmetic share conversion.
//     in0_i is a Boolean sharing (a0, a1) where a = a0 XOR a1.
//     result_o is an arithmetic sharing (b0, b1) where b = b0 + b1 mod mod_i = a.
//
//     Algorithm: draw a fresh random mask m = mask_mod (rejection-sampled to m < mod_i), push m
//     into the mask FIFO, then feed the adder:
//       adder_inp1 = in0_i            // Boolean sharing of a
//       adder_inp2 = (-m XOR r1, r1)  // Boolean sharing of -m
//     The adder yields a Boolean sharing of (a - m). The output reconstructs:
//       result_o[0] = m                  // Popped from the mask FIFO
//       result_o[1] = (a - m) mod mod_i  // XOR-sum of the otbn_sec_add_mod output
//     so result_o[0] + result_o[1] mod mod_i = a.
//
// All modes interpose a blanker + register stage between the input handshake and the adder to
// prevent share data from glitching into the adder while no valid transaction is in flight,
// adding one cycle of input latency. Two separate paths are required because in A2B the second
// arithmetic share (in0_i[1]) is routed to adder inp2 share 0, crossing share indices.
//
// Throughput and latency (SecAddWidth=32, Stages=5):
//   SecAdd:      1 sample/cycle
//                latency = 7 cycles (Stages+1 adder + 1 input register).
//   SecAddMod:   0.5 samples/cycle (VecSize=8 batch)
//                latency = 15 cycles to first result, 22 to last.
//   ArithToBool: same throughput and latency as SecAddMod.
//   BoolToArith: same throughput as SecAddMod
//                latency = 16 to first result, 23 to last (+1 output register cycle).
//                Rejection sampling may insert extra input cycles and decrease throughput.
//
// Rejection sampling (EnRejSampling=1, BoolToArith only):
//   wready_o is deasserted whenever mask_mod >= mod_i. The caller must hold wvalid_i high until
//   wready_o rises. Assert sec_wipe_running_i for SCA analysis to avoid trace misalignment, or set
//   EnRejSampling=0 for CocoAlma verification.
//
// Interface:
//   wvalid_i / wready_o : Input handshake following the 'valid locked-in' principle: once wvalid_i
//                         is asserted, in0_i and in1_i must remain stable until the handshake
//                         completes (wready_o sampled high). wready_o is deasserted during
//                         pass-2 for modular modes and during rejection-sampling stalls for
//                         BoolToArith.
//   rvalid_o            : Asserted when a valid result is at result_o. There is no output
//                         backpressure. Results must be consumed in the cycle rvalid_o is high.
//                         rready_i is present for interface uniformity but unused.
//   mod_i               : Modulus for A2B/B2A/SecAddMod correction and B2A rejection sampling.
//                         Must originate directly form a flop and must not change while a batch is
//                         in progress.
//   mask_op_i           : Operation selector. Must originate directly form a flop and must not
//                         change while a batch is in progress.
//   rand_i              : Fresh per-cycle randomness for the HPC3 gadgets.
//   remask_rand_i       : Fresh per-handshake randomness for input re-masking.
//   sec_wipe_running_i  : When asserted, disables rejection sampling so that a wipe can make
//                         forward progress regardless of mask_mod. Has no effect when
//                         EnRejSampling=0.
//
// Security verification: see hw/ip/otbn/pre_sca for PROLEAD and Alma setups.
//
// For details, see the following paper:
// Algorithm 8 in T. Fritzmann et al., "Masked Accelerators and Instruction Set Extensions for
// Post-Quantum Cryptography", available at:
// https://tches.iacr.org/index.php/TCHES/article/view/9303/8869

module otbn_mask_accelerator
  import otbn_pkg::*;
#(
  localparam int RandWidth     = SecAddRandWidth(SecAddWidth),
  parameter  bit EnRejSampling = 1
) (
  input  logic clk_i,
  input  logic rst_ni,

  // Flush trigger
  input  logic sec_wipe_running_i,

  // Write port
  input  logic        wvalid_i,
  output logic        wready_o,
  input  ma_sharing_t in0_i,
  input  ma_sharing_t in1_i,

  // Randomness
  input  logic [RandWidth-1:0] rand_i,
  input  ma_sharing_t          remask_rand_i,

  // Config
  input  ma_ele_t  mod_i,
  input  mask_op_e mask_op_i,

  // Read port
  output logic        rvalid_o,
  input  logic        rready_i,
  output ma_sharing_t result_o,

  // Errors
  output logic mask_fifo_err_o,
  output logic ctr_err_o
);

  // Input handshake.
  // inp_valid is delayed one cycle to become adder_wvalid.
  logic inp_ready;
  logic wready;
  logic inp_valid;
  logic inp_valid_q;

  // Modulus helpers shared across A2B and B2A pre-adder computations.
  ma_ele_t mod_neg;
  ma_ele_t mod_smear_mask;
  ma_ele_t mask_mod;

  // A2B input path: pre-computation -> blanker -> register.
  ma_sharing_t a2b_inp1_pre;
  ma_sharing_t a2b_inp2_pre;
  ma_sharing_t a2b_inp1_blanked;
  ma_sharing_t a2b_inp2_blanked;
  ma_sharing_t a2b_inp1_q;
  ma_sharing_t a2b_inp2_q;

  // Direct input path (B2A / SecAdd / SecAddMod): pre-computation -> blanker -> register.
  ma_sharing_t b2a_inp2_pre;
  ma_sharing_t direct_inp2_pre;
  ma_sharing_t direct_inp1_blanked;
  ma_sharing_t direct_inp2_blanked;
  ma_sharing_t direct_inp1_q;
  ma_sharing_t direct_inp2_q;

  // Adder interface: inputs, control, outputs.
  ma_sharing_t adder_inp1;
  ma_sharing_t adder_inp2;
  logic        adder_enable_mod;
  logic        adder_wvalid;
  logic        adder_wready;
  logic        adder_rvalid;
  logic        adder_batch_complete;
  ma_sharing_t adder_result;

  // B2A output path: FIFO / post-computation -> blanker -> register.
  ma_ele_t     fifo_rdata;
  logic        fifo_wready;
  ma_sharing_t result_b2a;
  ma_sharing_t result_b2a_q;
  logic        rvalid_b2a_d;
  logic        rvalid_b2a_q;

  // Assign unused input ports to avoid lint warnings.
  logic unused_rready;
  assign unused_rready = rready_i;

  // Two's complement of the modulus.
  assign mod_neg = -mod_i;

  always_comb begin : proc_mod_smear_mask
    mod_smear_mask = mod_i;
    // Smear all set bits rightward: after k iterations all bits below the highest set bit are 1.
    for (int ii = 0; ii < $clog2(SecAddWidth); ii++) begin
      mod_smear_mask = mod_smear_mask | (mod_smear_mask >> (1 << ii));
    end
  end

  // Mask remask_rand_i[0] to the bit-width of mod_i for rejection sampling.
  assign mask_mod = remask_rand_i[0] & mod_smear_mask;

  // Interpret handshake signals to determine the start of an adder operation.
  assign inp_valid    = wvalid_i && wready_o;
  assign adder_wvalid = inp_valid_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_inp_valid
    if (!rst_ni) begin
      inp_valid_q <= 1'b0;
    end else begin
      inp_valid_q <= inp_valid;
    end
  end

  // A2B input pre-encoding: produce fresh Boolean sharings of a0 and (a1 + mod_neg).
  //   inp1 = (a0 ^ r0, r0)
  //   inp2 = ((a1+mod_neg) ^ r1, r1)
  // The adder computes a0 + (a1 + mod_neg) = a + mod_neg.
  // SecAddMod's two-pass correction yields a Boolean masked a.
  assign a2b_inp1_pre[0] = in0_i[0] ^ remask_rand_i[0];
  assign a2b_inp1_pre[1] = remask_rand_i[0];
  assign a2b_inp2_pre[0] = (in0_i[1] + mod_neg) ^ remask_rand_i[1];
  assign a2b_inp2_pre[1] = remask_rand_i[1];

  // B2A input pre-encoding: inp1 is in0_i directly (already a Boolean sharing of a).
  // inp2 is a fresh Boolean sharing of -mask_mod:
  //   inp2 = ((-m) ^ r1, r1)
  // The adder computes a + (-m) = a - m.
  // The output creates an Arithmetic sharing with m popped from the FIFO.
  assign b2a_inp2_pre[0] = (-mask_mod) ^ remask_rand_i[1];
  assign b2a_inp2_pre[1] = remask_rand_i[1];

  // A2B blanker + flop: gate the A2B pre-computed inputs to zero outside A2B mode so that
  // stale or transitioning values cannot glitch into the adder pipeline when a different
  // operation is active. The register breaks the combinational path to the adder.
  prim_blanker #(
    .Width(NumShares*SecAddWidth)
  ) u_prim_blanker_a2b_inp1 (
    .in_i (a2b_inp1_pre),
    .en_i ((mask_op_i == ArithToBool) && inp_valid),
    .out_o(a2b_inp1_blanked)
  );
  prim_blanker #(
    .Width(NumShares*SecAddWidth)
  ) u_prim_blanker_a2b_inp2 (
    .in_i (a2b_inp2_pre),
    .en_i ((mask_op_i == ArithToBool) && inp_valid),
    .out_o(a2b_inp2_blanked)
  );

  prim_flop #(
    .Width(NumShares*SecAddWidth),
    .ResetValue('0)
  ) u_prim_flop_a2b_inp1 (
    .clk_i,
    .rst_ni,
    .d_i(a2b_inp1_blanked),
    .q_o(a2b_inp1_q)
  );
  prim_flop #(
    .Width(NumShares*SecAddWidth),
    .ResetValue('0)
  ) u_prim_flop_a2b_inp2 (
    .clk_i,
    .rst_ni,
    .d_i(a2b_inp2_blanked),
    .q_o(a2b_inp2_q)
  );

  // Direct blanker + flop (B2A / SecAdd / SecAddMod): gate inputs to zero in A2B mode so that
  // stale or transitioning values cannot glitch into the adder pipeline when A2B is active.
  // The register breaks the combinational path to the adder.
  // inp1 is always in0_i.
  // inp2 is mode-selected between B2A's pre-computed value and the raw in1_i.
  assign direct_inp2_pre = (mask_op_i == BoolToArith) ? b2a_inp2_pre : in1_i;

  prim_blanker #(
    .Width(NumShares*SecAddWidth)
  ) u_prim_blanker_direct_inp1 (
    .in_i (in0_i),
    .en_i ((mask_op_i != ArithToBool) && inp_valid),
    .out_o(direct_inp1_blanked)
  );
  prim_blanker #(
    .Width(NumShares*SecAddWidth)
  ) u_prim_blanker_direct_inp2 (
    .in_i (direct_inp2_pre),
    .en_i ((mask_op_i != ArithToBool) && inp_valid),
    .out_o(direct_inp2_blanked)
  );

  prim_flop #(
    .Width(NumShares*SecAddWidth),
    .ResetValue('0)
  ) u_prim_flop_direct_inp1 (
    .clk_i,
    .rst_ni,
    .d_i(direct_inp1_blanked),
    .q_o(direct_inp1_q)
  );
  prim_flop #(
    .Width(NumShares*SecAddWidth),
    .ResetValue('0)
  ) u_prim_flop_direct_inp2 (
    .clk_i,
    .rst_ni,
    .d_i(direct_inp2_blanked),
    .q_o(direct_inp2_q)
  );

  // Select adder inputs: A2B registered path or common registered path.
  always_comb begin : proc_adder_inp_sel
    adder_inp1 = direct_inp1_q;
    adder_inp2 = direct_inp2_q;
    if (mask_op_i == ArithToBool) begin
      adder_inp1 = a2b_inp1_q;
      adder_inp2 = a2b_inp2_q;
    end
  end

  assign adder_enable_mod = (mask_op_i != SecAdd);

  otbn_sec_add_mod #(
    .Width(SecAddWidth)
  ) u_otbn_sec_add_mod (
    .clk_i,
    .rst_ni,
    .rand_i,
    .modulus_i       (mod_i),
    .enable_mod_i    (adder_enable_mod),
    .wready_o        (adder_wready),
    .wvalid_i        (adder_wvalid),
    .inp1_i          (adder_inp1),
    .inp2_i          (adder_inp2),
    .result_o        (adder_result),
    .rvalid_o        (adder_rvalid),
    .batch_complete_o(adder_batch_complete),
    .ctr_err_o
  );

  // Mask FIFO: stores mask_mod values pushed during BoolToArith batches.
  // Popped when the corresponding adder result exits the pipeline (signalled by rvalid_b2a_q).
  // Pass=0: passthrough disabled so the depth counter is only driven by genuine handshakes.
  prim_fifo_sync #(
    .Width(SecAddWidth),
    .Pass (1'b0),
    .Depth(SecAddVecSize),
    .Secure(1'b1)
  ) u_prim_fifo_sync_mask (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(inp_valid && (mask_op_i == BoolToArith)),
    .wready_o(fifo_wready),
    .wdata_i (mask_mod),
    .rvalid_o(),
    .rready_i(rvalid_b2a_q),
    .rdata_o (fifo_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   (mask_fifo_err_o)
  );

  // B2A output blanker + flop: gate the adder result to zero outside B2A mode so that results
  // from other operations cannot glitch into the B2A output path. The shares are masked with
  // mod_smear_mask before blanking to zero bits above mod_i's MSB. The register breaks the
  // combinational path from the adder to the output XOR.
  prim_blanker #(
    .Width(NumShares*SecAddWidth)
  ) u_prim_blanker_result (
    .in_i ({adder_result[0] & mod_smear_mask, adder_result[1] & mod_smear_mask}),
    .en_i ((mask_op_i == BoolToArith) && adder_rvalid),
    .out_o(result_b2a)
  );

  prim_flop #(
    .Width(NumShares*SecAddWidth),
    .ResetValue('0)
  ) u_prim_flop_result_b2a (
    .clk_i,
    .rst_ni,
    .d_i(result_b2a),
    .q_o(result_b2a_q)
  );

  // Mode-gated: prevents spurious FIFO pops in non-B2A modes.
  assign rvalid_b2a_d = adder_rvalid && (mask_op_i == BoolToArith);

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_rvalid_b2a
    if (!rst_ni) begin
      rvalid_b2a_q <= 1'b0;
    end else begin
      rvalid_b2a_q <= rvalid_b2a_d;
    end
  end

  // Assign input and output signals based on the selected mask operation.
  always_comb begin : proc_output_mux
    // A2B, SecAdd, SecAddMod modes.
    inp_ready = adder_wready && !adder_batch_complete;
    result_o  = adder_result;
    rvalid_o  = adder_rvalid;
    if (mask_op_i == BoolToArith) begin
      // B2A mode.
      inp_ready   = fifo_wready && adder_wready && !adder_batch_complete;
      // result_o[0] = m (arithmetic mask, popped from the FIFO)
      // result_o[1] = (a - m) mod mod_i (masked secret, XOR of the two boolean shares).
      result_o[0] = fifo_rdata;
      result_o[1] = result_b2a_q[0] ^ result_b2a_q[1];
      rvalid_o    = rvalid_b2a_q;
    end
  end

  assign wready = inp_ready;
  // sec_wipe_running_i disables rejection sampling so that a wipe can always make forward
  // progress regardless of mask_mod.
  if (EnRejSampling) begin : gen_rej_sampling
    assign wready_o = (mask_op_i == BoolToArith && !sec_wipe_running_i) ?
                      (mask_mod < mod_i) && wready : wready;
  end else begin : gen_no_rej_sampling
    logic unused_sec_wipe;
    assign unused_sec_wipe = sec_wipe_running_i;
    assign wready_o = wready;
  end

  // wvalid_i follows the 'valid locked-in' principle: once asserted it must not fall until
  // wready_o is sampled high.
  `ASSERT(WvalidLockedIn_A, wvalid_i && !wready_o |=> wvalid_i)

endmodule
