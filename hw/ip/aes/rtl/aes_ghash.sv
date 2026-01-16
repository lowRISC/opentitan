// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES GHASH implementation for AES-GCM
//
// This module implements the GHASH core including hash state and hash key register required for
// AES-GCM.
//
// Details on the data formats
// ---------------------------
//
// The aes_core as well as the aes_cipher_core modules use 4-dimensional SystemVerilog arrays to
// represent AES states:
//
//   logic [3:0][3:0][7:0] state_q [NumShares];
//
// The fourth dimension (unpacked) corresponds to the different shares. The first element holds the
// (masked) data share whereas the other elements hold the masks (masked implementation only).
// The three packed dimensions correspond to the 128-bit state matrix per share. This
// implementation uses the same encoding as the Advanced Encryption Standard (AES) FIPS Publication
// 197 available at https://www.nist.gov/publications/advanced-encryption-standard-aes (see Section
// 3.4). An input sequence of 16 bytes (128-bit, left most byte is the first one)
//
//   B0 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15
//
// is mapped to the state matrix as
//
//   [ B0  B4  B8  B12 ]
//   [ B1  B5  B9  B13 ]
//   [ B2  B6  B10 B14 ]
//   [ B3  B7  B11 B15 ] .
//
// In contrast, this implementation of the GHASH module uses 2-dimensional SystemVerilog arrays
// to represent bit strings:
//
//   logic [127:0] hash_subkey_q [NumShares];
//
// The second dimension (unpacked) corresponds to the different shares. The first element holds
// the (masked) data share whereas the other elements hold the masks (masked implementation only).
// The unpacked dimension corresponds to the 128-bit bit string per share. This implementation
// uses the same encoding as Recommendation for Block Cipher Modes of Operation: Galois/Counter
// Mode (GCM) and GMAC NIST Special Publication 800-38D available at
// https://csrc.nist.gov/pubs/sp/800/38/d/final (See Section 6.1) and as Advanced Encryption
// Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes (see Section 3.3). An input
// sequence of 128 bits (left most bit is the first one)
//
//   b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 ... b125 b126 b127
//
// is mapped to Bytes as follows
//
//   B0  = {b0   b1   b2   b3   b4   b5   b6   b7  }
//   B1  = {b8   b9   b10  b11  b12  b13  b14  b15 }
//   .
//   B15 = {b120 b121 b122 b123 b124 b125 b126 b127} .
//
// Internally, this is mapped to the 128-bit packed dimension of the SystemVerilog array as follows
//
//          /-------- Byte 0 --------\      ...      /-------- Byte 15 -------\
//   128'b{ b0, b1, b2, ... b5, b6, b7, b8, b9, ..., b119, b120, ... b126, b127 }
//
// meaning the hexadecimal representations of these values can directly be compared with test vector
// data found in The Galois/Counter Mode of Operation (GCM) available at
// https://csrc.nist.rip/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf (See
// Appendix B).
//
// However, when interfacing the GF(2^128) multiplier, the bit order has to reversed to obtain
// packed 128-bit SystemVerilog arrays with the MSB left and the LSB right, i.e.,
//
//   128'b{ b127, b126, ... b1, b0 } .
//
// The final authentication tag is put out via Data Out registers and uses again the above format
//
//                    MSB         LSB
// - DATA_OUT_0 32'h{ B3  B2  B1  B0  }
// - DATA_OUT_1 32'h{ B7  B6  B5  B4  }
// - DATA_OUT_2 32'h{ B11 B10 B9  B8  }
// - DATA_OUT_3 32'h{ B15 B14 B13 B12 }
//
// Or in terms of bits
//                                                      MSB       LSB
// - DATA_OUT_0 32'h = 32'h{ b24 b25 b26 b27 b28 b29 b30 b31 ...  b0 b1 b2 b3 b4 b5 b6 b7 }
// - ...

`include "prim_assert.sv"

module aes_ghash
  import aes_pkg::*;
  import aes_reg_pkg::*;
#(
  parameter bit          SecMasking   = 1,
  parameter int unsigned GFMultCycles = 32,

  localparam int         NumShares    = SecMasking ? 2 : 1 // derived parameter
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,

  // Input handshake signals
  input  sp2v_e                        in_valid_i,
  output sp2v_e                        in_ready_o,

  // Output handshake signals
  output sp2v_e                        out_valid_o,
  input  sp2v_e                        out_ready_i,

  // Control signals
  input  aes_op_e                      op_i,
  input  gcm_phase_e                   gcm_phase_i,
  input  logic [4:0]                   num_valid_bytes_i,
  input  sp2v_e                        load_hash_subkey_i,
  input  logic                         clear_i,
  output logic                         first_block_o,
  input  logic                         alert_fatal_i,
  output logic                         alert_o,

  // I/O data signals
  input  logic         [GCMDegree-1:0] data_in_prev_i,                  // Ciphertext for decryption
                                                                        // or AAD
  input  logic [NumRegsData-1:0][31:0] data_out_i,                      // Ciphertext for encryption
  input  logic         [3:0][3:0][7:0] cipher_state_done_i [NumShares], // Masked cipher core output
  output logic [NumRegsData-1:0][31:0] ghash_state_done_o
);

  // Parameters
  localparam int GFMultStagesPerCycle = GCMDegree / GFMultCycles;

  // Signals
  logic [GCMDegree-1:0] s_d;
  logic [GCMDegree-1:0] s_q;
  sp2v_e                s_we;
  logic [GCMDegree-1:0] corr_d [2];
  logic [GCMDegree-1:0] corr_q [2];
  sp2v_e                corr_we;
  logic                 corr0_en_d;
  logic                 corr0_en_q;
  logic [15:0][7:0]     ghash_in;
  logic [15:0][7:0]     ghash_in_valid;
  ghash_in_sel_e        ghash_in_sel;
  ghash_add_in_sel_e    ghash_add_in_sel_d [2];
  ghash_add_in_sel_e    ghash_add_in_sel_q [2];
  logic [1:0]           ghash_add_in_sel_err;
  logic [GCMDegree-1:0] ghash_state_d [NumShares];
  logic [GCMDegree-1:0] ghash_state_q [NumShares];
  logic [GCMDegree-1:0] add_s_in;
  logic                 add_s_en_d;
  logic                 add_s_en_q;
  logic [GCMDegree-1:0] ghash_state_done;
  logic [GCMDegree-1:0] ghash_state_add [NumShares];
  sp2v_e                ghash_state_we [2];
  ghash_state_sel_e     ghash_state_sel;
  logic [GCMDegree-1:0] ghash_state_mult [NumShares];
  logic [GCMDegree-1:0] hash_subkey_d [NumShares];
  logic [GCMDegree-1:0] hash_subkey_q [NumShares];
  sp2v_e                hash_subkey_we;
  logic                 gf_mult0_en_d;
  logic                 gf_mult0_en_q;
  gf_mult_in_sel_e      gf_mult1_in_sel_d;
  gf_mult_in_sel_e      gf_mult1_in_sel_q;
  logic                 gf_mult1_in_sel_err;
  logic [1:0]           gf_mult_req;
  logic [1:0]           gf_mult_ack;
  logic [1:0]           gf_mult_ack_pre;
  aes_ghash_e           aes_ghash_ns, aes_ghash_cs;
  logic                 first_block_d;
  logic                 first_block_q;
  logic                 final_add_d;
  logic                 final_add_q;
  logic                 advance;

  //////////////////////////////////
  // Input Data Format Conversion //
  //////////////////////////////////
  // Covert the input data to the internal data format.
  logic [GCMDegree-1:0] cipher_state_done [NumShares];
  logic [GCMDegree-1:0] data_in_prev;
  logic [GCMDegree-1:0] data_out;
  always_comb begin : data_in_conversion
    for (int s = 0; s < NumShares; s++) begin
      cipher_state_done[s] = aes_state_to_ghash_vec(cipher_state_done_i[s]);
    end
    data_in_prev = aes_state_to_ghash_vec(aes_transpose(data_in_prev_i));
    data_out     = aes_state_to_ghash_vec(aes_transpose(data_out_i));
  end

  ////////////////////
  // S = AES_K(J_0) //
  ////////////////////
  // The initial counter block J_0 encrypted using the encryption key K. For the unmasked
  // implementation this is only used at the very end.
  //
  // For the masked implementaion, the shares of S are used multiple times in the form of
  // correction terms throughout the entire computation (see separate section below for details).
  // In addition, Share 1 of S only is again used at the very end.
  //
  // These registers can be cleared with pseudo-random data by loading the output of the cipher
  // core after having cleared the internal state of the cipher core.
  if (SecMasking) begin : gen_s1
    // Save Share 1 of S for later usage.
    assign s_d = cipher_state_done[1];

  end else begin : gen_s0
    // S comes in unmasked, simply save it.
    assign s_d = cipher_state_done[0];
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : s_reg
    if (!rst_ni) begin
      s_q <= '0;
    end else if (s_we == SP2V_HIGH) begin
      s_q <= s_d;
    end
  end

  //////////////////////
  // Correction Terms //
  //////////////////////
  // For the masked implementation, three correction terms based on the Shares of S as well as on
  // the Shares of the sub hashkey need to be added to various intermediate results. Two of these
  // correction terms are added repeatedly. These are thus stored in dedicated registers. A third
  // correction term is used only once, it is computed on demand. The following terms are needed:
  //
  // 1. (S0 * H0) + S0 -- Used for every block, computed during the initialization phase.
  // 2.  S0 * H1       -- Used for every block except for the first one, computed during the
  //                      initialization phase.
  // 3.  S1 * H1       -- Used only for the first block and computed on demand.
  //
  // where S0 or S1 is Share 0 or Share 1 of S, respectively. Similarly, H0 or H1 is Share 0 or
  // Share 1 of the hash subkey, respectively.
  //
  // These registers can be cleared after pushing some pseudo-random data through the multipliers.
  if (SecMasking) begin : gen_corr_terms
    // Avoid glichtes on the enable signal controlling the blanking.
    prim_flop #(
      .Width     (1),
      .ResetValue(1'b0)
    ) u_prim_flop_corr0_en (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .d_i(corr0_en_d),
      .q_o(corr0_en_q)
    );

    // Only feed Share 0 of the GHASH state into the addition if we're actually updating the
    // correction terms. This helps reducing undesirable SCA leakage due to combining intermediate
    // results of the first mutliplier (when not computing correction terms) with the GHASH state.
    logic [GCMDegree-1:0] ghash_state0_blanked;
    prim_blanker #(
      .Width(GCMDegree)
    ) u_prim_blanker_corr0 (
      .in_i (ghash_state_q[0]),
      .en_i (corr0_en_q),
      .out_o(ghash_state0_blanked)
    );

    assign corr_d[0] = ghash_state_mult[0] ^ ghash_state0_blanked;
    assign corr_d[1] = ghash_state_mult[1];

    always_ff @(posedge clk_i or negedge rst_ni) begin : corr_reg
      if (!rst_ni) begin
        corr_q <= '{default: '0};
      end else if (corr_we == SP2V_HIGH) begin
        corr_q <= corr_d;
      end
    end
  end

  /////////////////
  // GHASH Input //
  /////////////////
  // Select the ciphertext for encryption / decryption.
  always_comb begin : ghash_in_mux
    unique case (ghash_in_sel)
      GHASH_IN_DATA_IN_PREV: ghash_in = data_in_prev;
      GHASH_IN_DATA_OUT:     ghash_in = data_out;
      default:               ghash_in = data_out;
    endcase
  end

  // Mask invalid bytes. The least significant byte is mapped to Position 15 internally. See
  // the section "Details on the data formats" in the header for details.
  always_comb begin
    for (int unsigned i = 0; i < 16; i++) begin
      ghash_in_valid[15-i] = num_valid_bytes_i > i[4:0] ? ghash_in[15-i] : 8'b0;
    end
  end

  /////////////////
  // GHASH State //
  /////////////////
  // Add the GHASH input or correction terms (masked implementation only) to the current state.
  if (SecMasking) begin : gen_masked_add
    logic [GCMDegree-1:0] add_in [NumShares];

    // Depending on the which phase we are in, we either add the GHASH input, or some correction
    // term to the GHASH state. The selection may vary between the two shares. To reduce
    // undesirable SCA leakage due to the multiplexing, prim_onehot_mux instances are used.
    logic [GHashAddInSelWidth-1:0] ghash_add_in_sel_q_raw [NumShares];
    logic          [GCMDegree-1:0] ghash_add_in_mux_in [NumShares][GHashAddInSelWidth];

    // The actual one-hot multiplexer forward any of the three inputs or zero if no input is
    // selected (ghash_add_in_sel_q[i] == ADD_IN_ZERO).
    assign ghash_add_in_mux_in[0][0] = ghash_in_valid;
    assign ghash_add_in_mux_in[0][1] = corr_q[0];
    assign ghash_add_in_mux_in[0][2] = ghash_state_q[1];

    assign ghash_add_in_mux_in[1][0] = ghash_in_valid;
    assign ghash_add_in_mux_in[1][1] = corr_q[1];
    assign ghash_add_in_mux_in[1][2] = ghash_state_mult[1];

    for (genvar s = 0; s < NumShares; s++) begin : gen_add_in_muxes
      // Avoid glichtes on the selector signals.
      prim_flop #(
        .Width     (GHashAddInSelWidth),
        .ResetValue({ADD_IN_GHASH_IN})
      ) u_prim_flop_add_in_sel (
        .clk_i (clk_i),
        .rst_ni(rst_ni),

        .d_i({ghash_add_in_sel_d[s]}),
        .q_o(ghash_add_in_sel_q_raw[s])
      );
      assign ghash_add_in_sel_q[s] = ghash_add_in_sel_e'(ghash_add_in_sel_q_raw[s]);

      // Check that the selector signals are indeed one-hot encoded or zero.
      prim_onehot_check #(
        .OneHotWidth(GHashAddInSelWidth),
        .AddrCheck  (1'b0),
        .StrictCheck(1'b0)
      ) u_prim_onehot_check_add_in_sel (
        .clk_i (clk_i),
        .rst_ni(rst_ni),

        .oh_i  ({ghash_add_in_sel_q[s]}),
        .addr_i('0),
        .en_i  (1'b1),
        .err_o (ghash_add_in_sel_err[s])
      );

      // The actual mux.
      prim_onehot_mux #(
        .Width (GCMDegree),
        .Inputs(GHashAddInSelWidth)
      ) u_prim_onehot_mux_add_in (
        .clk_i (clk_i),
        .rst_ni(rst_ni),

        .in_i (ghash_add_in_mux_in[s]),
        .sel_i(ghash_add_in_sel_q[s]),
        .out_o(add_in[s])
      );
    end

    // Perform the addition on a per-share basis.
    for (genvar s = 0; s < NumShares; s++) begin : gen_state_add
      assign ghash_state_add[s] = ghash_state_q[s] ^ add_in[s];
    end

  end else begin : gen_unmasked_add

    // Simply add the GHASH input to the current state.
    assign ghash_state_add[0] = ghash_state_q[0] ^ ghash_in_valid;
  end

  // The GHASH state muxing differs in the number of inputs between the masked and the unmasked
  // implementation.
  if (SecMasking) begin : gen_ghash_state_mux_masked

    // We initialize the state with S.
    //
    // For restoring a GHASH state, we overwrite Share 0 of the initialized GHASH state with the
    // previously saved value in unmasked form, i.e. GHASH state + S. Share 1 is left untouched.
    // This is equal to subtracing Share 1 of S which will be added again at the very end. To save
    // muxing resources, Share 1 of the state multiplexer below is identical to the default.
    always_comb begin : ghash_state0_mux
      unique case (ghash_state_sel)
        GHASH_STATE_INIT:    ghash_state_d[0] = cipher_state_done[0];
        GHASH_STATE_RESTORE: ghash_state_d[0] = data_in_prev;
        GHASH_STATE_ADD:     ghash_state_d[0] = ghash_state_add[0];
        GHASH_STATE_MULT:    ghash_state_d[0] = ghash_state_mult[0];
        // GHASH_STATE_ADD_S unused.
        default:             ghash_state_d[0] = ghash_state_add[0];
      endcase
    end
    always_comb begin : ghash_state1_mux
      unique case (ghash_state_sel)
        GHASH_STATE_INIT:    ghash_state_d[1] = cipher_state_done[1];
        GHASH_STATE_ADD:     ghash_state_d[1] = ghash_state_add[1];
        GHASH_STATE_MULT:    ghash_state_d[1] = ghash_state_mult[1];
        // GHASH_STATE_RESTORE and GHASH_STATE_ADD_S unused.
        default:             ghash_state_d[1] = ghash_state_add[1];
      endcase
    end

  end else begin : gen_ghash_state_mux_unmasked

    // We initialize the state with S. In case of the unmasked implementation, S has to be
    // substracted in a second step to reach the required zero state. Doing it this way allows
    // saving one multiplexer input.
    //
    // For restoring a GHASH state in the unmasked implementation, the previously saved value,
    // i.e., GHASH state + S, is added to the GHASH state initialized to 0. S is then substracted
    // again seperately. Doing this allows saving one multiplexer input.
    //
    // The resulting multiplexer has 4 inputs.
    always_comb begin : ghash_state_mux
      unique case (ghash_state_sel)
        GHASH_STATE_RESTORE: ghash_state_d[0] = ghash_state_add[0];
        GHASH_STATE_INIT:    ghash_state_d[0] = cipher_state_done[0];
        GHASH_STATE_ADD:     ghash_state_d[0] = ghash_state_add[0];
        GHASH_STATE_ADD_S:   ghash_state_d[0] = ghash_state_done;
        GHASH_STATE_MULT:    ghash_state_d[0] = ghash_state_mult[0];
        // GHASH_STATE_RESTORE is equal to GHASH_STATE_ADD.
        default:             ghash_state_d[0] = ghash_state_add[0];
      endcase
    end
  end

  // This register can be cleared with pseudo-random data by adding the output of the cipher core
  // to the current state after having cleared the internal state of the cipher core.
  for (genvar s = 0; s < NumShares; s++) begin : gen_ghash_state_reg_shares
    always_ff @(posedge clk_i or negedge rst_ni) begin : ghash_state_reg
      if (!rst_ni) begin
        ghash_state_q[s] <= '0;
      end else if (ghash_state_we[s] == SP2V_HIGH) begin
        ghash_state_q[s] <= ghash_state_d[s];
      end
    end
  end

  /////////////////
  // Hash Subkey //
  /////////////////
  // This register can be cleared with pseudo-random data by loading the output of the cipher
  // core after having cleared the internal state of the cipher core.
  assign hash_subkey_d = cipher_state_done;
  always_ff @(posedge clk_i or negedge rst_ni) begin : hash_subkey_reg
    if (!rst_ni) begin
      hash_subkey_q <= '{default: '0};
    end else if (hash_subkey_we == SP2V_HIGH) begin
      hash_subkey_q <= hash_subkey_d;
    end
  end

  //////////////////////////
  // GF(2^128) Multiplier //
  //////////////////////////
  logic [GCMDegree-1:0] gf_mult_op_b[NumShares];
  logic [GCMDegree-1:0] gf_mult_op_b_rev[NumShares];
  logic [GCMDegree-1:0] gf_mult_prod[NumShares];

  // The first multiplier has no muxes on the operand inputs. For the masked implementation,
  // a prim_blanker instance helps to reduce undesirable SCA leakage.
  if (SecMasking) begin : gen_gf_mult0_blanker
    // Avoid glichtes on the enable signal controlling the blanking.
    prim_flop #(
      .Width     (1),
      .ResetValue(1'b0)
    ) u_prim_flop_gf_mult0_en (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .d_i(gf_mult0_en_d),
      .q_o(gf_mult0_en_q)
    );

    // Only present a non-zero input if we're actually performing a multiplication.
    prim_blanker #(
      .Width(GCMDegree)
    ) u_prim_blanker_gf_mult0 (
      .in_i (ghash_state_q[0]),
      .en_i (gf_mult0_en_q),
      .out_o(gf_mult_op_b[0])
    );
  end else begin : gen_no_gf_mult0_blanker
    assign gf_mult_op_b[0] = ghash_state_q[0];
  end

  // Reverse the bit order.
  assign gf_mult_op_b_rev[0] = aes_ghash_reverse_bit_order(gf_mult_op_b[0]);

  if (SecMasking) begin : gen_gf_mult1_mux
    // The second multiplier is used to multiply Share 1 of the hash subkey with Share 0,
    // Share 1 (first block only) of the state, and also Share 1 of S. To reduce undesirable SCA
    // leakage due to the multiplexing, a prim_onehot_mux instance is used.
    logic [GFMultInSelWidth-1:0] gf_mult1_in_sel_q_raw;
    logic        [GCMDegree-1:0] gf_mult1_op_b_mux_in [GFMultInSelWidth];

    // Avoid glitches on the selector signal.
    prim_flop #(
      .Width     (GFMultInSelWidth),
      .ResetValue({MULT_IN_ZERO})
    ) u_prim_flop_gf_mult1_in_sel (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .d_i({gf_mult1_in_sel_d}),
      .q_o(gf_mult1_in_sel_q_raw)
    );
    assign gf_mult1_in_sel_q = gf_mult_in_sel_e'(gf_mult1_in_sel_q_raw);

    // Check that the selector signal is indeed one-hot encoded or zero.
    prim_onehot_check #(
      .OneHotWidth(GFMultInSelWidth),
      .AddrCheck  (1'b0),
      .StrictCheck(1'b0)
    ) u_prim_onehot_check_gf_mult1_in_sel (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .oh_i  ({gf_mult1_in_sel_q}),
      .addr_i('0),
      .en_i  (1'b1),
      .err_o (gf_mult1_in_sel_err)
    );

    // The actual one-hot multiplexer forwards any of the three inputs or zero if no input is
    // selected (gf_mult1_in_sel_q == MULT_IN_ZERO).
    assign gf_mult1_op_b_mux_in[0] = ghash_state_q[0];
    assign gf_mult1_op_b_mux_in[1] = ghash_state_q[1];
    assign gf_mult1_op_b_mux_in[2] = s_q;
    prim_onehot_mux #(
      .Width (GCMDegree),
      .Inputs(GFMultInSelWidth)
    ) u_prim_onehot_mux_gf_mult1_op_b (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .in_i (gf_mult1_op_b_mux_in),
      .sel_i(gf_mult1_in_sel_q),
      .out_o(gf_mult_op_b[1])
    );

    // Reverse the bit order.
    logic [GCMDegree-1:0] gf_mult1_op_b_rev;
    assign gf_mult1_op_b_rev = aes_ghash_reverse_bit_order(gf_mult_op_b[1]);

    // Register the last input slice of Operand B. This allows switching the one-hot multiplexer
    // during the last clock cycle of the multiplication to effectively flush the multiplexer. This
    // is beneficial from a SCA hardening viewpoint for two reasons:
    // - Flushing the multiplexer before providing the next input avoids leakage between
    //   different multiplexer inputs and enables back-to-back multiplications.
    // - Upon the last multiplication cycle, the GHASH state is updated. Even if the Operand B
    //   input of the multiplier is blanked in the next clock cycle, transient effects may cause
    //   the updated GHASH state to propagate into the multiplier and be combined with the secret
    //   hash subkey which can cause undesirable leakage.
    logic [GFMultStagesPerCycle-1:0] gf_mult1_op_b_rev_slice_d;
    logic [GFMultStagesPerCycle-1:0] gf_mult1_op_b_rev_slice_q;
    assign gf_mult1_op_b_rev_slice_d = gf_mult1_op_b_rev[GCMDegree-1 -: GFMultStagesPerCycle];
    always_ff @(posedge clk_i or negedge rst_ni) begin : gf_mult1_op_b_slice_reg
      if (!rst_ni) begin
        gf_mult1_op_b_rev_slice_q <= '0;
      end else begin
        gf_mult1_op_b_rev_slice_q <= gf_mult1_op_b_rev_slice_d;
      end
    end

    assign gf_mult_op_b_rev[1] =
        {gf_mult1_op_b_rev_slice_q, gf_mult1_op_b_rev[GCMDegree-GFMultStagesPerCycle-1:0]};
  end

  for (genvar s = 0; s < NumShares; s++) begin : gen_gf_mult
    prim_gf_mult #(
      .Width             (GCMDegree),
      .StagesPerCycle    (GFMultStagesPerCycle),
      .IPoly             (GCMIPoly),
      .OutputZeroUntilAck(1'b1)
    ) u_gf_mult (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .req_i(gf_mult_req[s]),
      .ack_o(gf_mult_ack[s]),

      .ack_pre_o(gf_mult_ack_pre[s]),

      .operand_a_i(aes_ghash_reverse_bit_order(hash_subkey_q[s])), // The A input is not scanned.
      .operand_b_i(gf_mult_op_b_rev[s]),                           // The B input is scanned.

      .prod_o(gf_mult_prod[s])
    );
    assign ghash_state_mult[s] = aes_ghash_reverse_bit_order(gf_mult_prod[s]);
  end

  if (!SecMasking) begin : gen_tie_offs
    // Tie-off datapath signals unused for the unmasked implementation.
    logic [GCMDegree-1:0] unused_corr_q [2];
    sp2v_e                unused_corr_we;
    assign corr_d         = '{default: '0};
    assign corr_q         = corr_d;
    assign unused_corr_q  = corr_q;
    assign unused_corr_we = corr_we;

    logic unused_corr0_en_q;
    assign corr0_en_q        = corr0_en_d;
    assign unused_corr0_en_q = corr0_en_q;

    logic unused_ghash_add_in_sel_d;
    assign unused_ghash_add_in_sel_d = ^{{ghash_add_in_sel_d[0]}, {ghash_add_in_sel_d[1]}};
    assign ghash_add_in_sel_q        = '{default: ADD_IN_GHASH_IN};
    assign ghash_add_in_sel_err      = 2'b00;
    assign gf_mult1_in_sel_err       = 1'b0;

    sp2v_e unused_ghash_state_we;
    assign unused_ghash_state_we = ghash_state_we[1];

    logic unused_gf_mult_req;
    assign unused_gf_mult_req = gf_mult_req[1];
    assign gf_mult_ack[1]     = 1'b1;
    assign gf_mult_ack_pre[1] = 1'b1;

    logic unused_add_s_en_q;
    assign add_s_en_q        = add_s_en_d;
    assign unused_add_s_en_q = add_s_en_q;
  end

  /////////////////
  // Control FSM //
  /////////////////

  always_comb begin : aes_ghash_fsm

    // Handshake signals
    in_ready_o  = SP2V_LOW;
    out_valid_o = SP2V_LOW;

    // Data path
    s_we       = SP2V_LOW;
    corr_we    = SP2V_LOW;
    corr0_en_d = 1'b0;

    ghash_in_sel = GHASH_IN_DATA_OUT;

    ghash_add_in_sel_d = ghash_add_in_sel_q;

    ghash_state_sel   = GHASH_STATE_ADD;
    ghash_state_we[0] = SP2V_LOW;
    ghash_state_we[1] = SP2V_LOW;

    hash_subkey_we = SP2V_LOW;

    gf_mult_req       = '0;
    gf_mult0_en_d     = gf_mult0_en_q;
    gf_mult1_in_sel_d = gf_mult1_in_sel_q;

    add_s_en_d = 1'b0;

    // FSM
    aes_ghash_ns  = aes_ghash_cs;
    first_block_d = first_block_q;
    final_add_d   = final_add_q;
    advance       = 1'b0;

    // Alert
    alert_o = 1'b0;

    unique case (aes_ghash_cs)
      GHASH_IDLE: begin
        in_ready_o = SP2V_HIGH;
        if (in_valid_i == SP2V_HIGH) begin
          if (clear_i) begin
            // Clearing has highest priority. In case of the masked implementation, we clear the
            // state using the initial state (the cipher core output, for which both shares are
            // random at this point). For the unmasked implementation, we use the unmasked cipher
            // core output.
            s_we              = SP2V_HIGH;
            ghash_state_sel   = SecMasking ? GHASH_STATE_INIT : GHASH_STATE_ADD;
            ghash_state_we[0] = SP2V_HIGH;
            ghash_state_we[1] = SP2V_HIGH;
            hash_subkey_we    = SP2V_HIGH;
            first_block_d     = 1'b1;
            final_add_d       = 1'b0;

            // In case of the masked implementation, also the correction terms need to be cleared.
            // This can be done by using the multipliers.
            if (SecMasking) begin
              gf_mult0_en_d     = 1'b1;
              gf_mult1_in_sel_d = MULT_IN_STATE0;
              aes_ghash_ns      = GHASH_MASKED_INIT;
            end

          end else if (gcm_phase_i == GCM_INIT) begin
            if (load_hash_subkey_i == SP2V_HIGH) begin

              // Load the hash subkey.
              hash_subkey_we  = SP2V_HIGH;
            end else begin

              // Load S and initialize the state with S.
              s_we              = SP2V_HIGH;
              ghash_state_sel   = GHASH_STATE_INIT;
              ghash_state_we[0] = SP2V_HIGH;
              ghash_state_we[1] = SP2V_HIGH;
              first_block_d     = 1'b1;

              // We have now all pre-requisites to compute the correction terms for the masked
              // implementation. For the unmasked implementation, we now have to subtract S again
              // from the state. Doing it this way allows saving one multiplexer input.
              if (SecMasking) begin
                gf_mult0_en_d     = 1'b1;
                gf_mult1_in_sel_d = MULT_IN_STATE0;
                aes_ghash_ns      = GHASH_MASKED_INIT;
              end else begin
                aes_ghash_ns      = GHASH_ADD_S;
              end
            end

          end else if (gcm_phase_i == GCM_RESTORE) begin
            // Restore a previously loaded GHASH state. We overwrite the Share 0 of the GHASH
            // state and leave Share 1 untouched. For the masked implementation, this is equal to
            // subtracting Share 1 of S. It is only added at the very end (or when saving the GHASH
            // state).
            ghash_state_sel   = GHASH_STATE_RESTORE;
            ghash_state_we[0] = SP2V_HIGH;
            first_block_d     = 1'b0;

            // For the unmasked implementation, the previously saved value, i.e., GHASH state + S,
            // is added to the GHASH state initialized to 0. S needs then to be substracted again
            // seperately before continuing.
            ghash_in_sel = !SecMasking ? GHASH_IN_DATA_IN_PREV : GHASH_IN_DATA_OUT;
            aes_ghash_ns = !SecMasking ? GHASH_ADD_S           : GHASH_IDLE;

          end else if (gcm_phase_i == GCM_AAD ||
                       gcm_phase_i == GCM_TEXT ||
                       gcm_phase_i == GCM_TAG) begin
            // Select the proper input for the addition.
            ghash_in_sel    =
                (gcm_phase_i == GCM_AAD)                     ? GHASH_IN_DATA_IN_PREV :
                (gcm_phase_i == GCM_TEXT && op_i == AES_DEC) ? GHASH_IN_DATA_IN_PREV :
                (gcm_phase_i == GCM_TEXT && op_i == AES_ENC) ? GHASH_IN_DATA_OUT     :
                (gcm_phase_i == GCM_TAG)                     ? GHASH_IN_DATA_IN_PREV :
                                                               GHASH_IN_DATA_OUT;

            // Add the current input to the GHASH state to start the multiplication afterwards.
            // Only for the first block both shares of the GHASH state need to be updated.
            ghash_state_we[0] = SP2V_HIGH;
            ghash_state_we[1] = first_block_q ? SP2V_HIGH : SP2V_LOW;

            if (SecMasking && !first_block_q) begin
              // In case masking is enabled and we've already done the first block, we have to do
              // one more addition before starting the multiplication.
              ghash_add_in_sel_d[0] = ADD_IN_CORR_B;
              aes_ghash_ns          = GHASH_MASKED_ADD_STATE_SHARES;
            end else begin

              // Start the multiplication. For the masked implementation, the second multiplier
              // takes Share 1 only for the very first block.
              gf_mult0_en_d     = 1'b1;
              gf_mult1_in_sel_d = MULT_IN_STATE1;
              aes_ghash_ns      = GHASH_MULT;
            end

          end else if (gcm_phase_i == GCM_SAVE) begin
            // Get ready to output the current GHASH state.

            // For the masked implementation, first unmask the GHASH state and then add Share 1 of
            // S. For the unmasked implementation, add S directly.
            final_add_d  = 1'b1;
            if (SecMasking) begin
              ghash_add_in_sel_d[0] = ADD_IN_CORR_B;
              aes_ghash_ns          = GHASH_MASKED_ADD_STATE_SHARES;
            end else begin
              add_s_en_d   = 1'b1;
              aes_ghash_ns = GHASH_OUT;
            end

          end else begin
            // Handshake without a valid command. We should never get here. If we do (e.g. via a
            // malicious glitch), error out immediately.
            aes_ghash_ns = GHASH_ERROR;
          end
        end
      end

      GHASH_MASKED_INIT: begin
        // Compute repeatedly used correction terms (masked implementation only). We need:
        //
        // 1. (S0 * H0) + S0
        // 2.  S0 * H1
        //
        // S0 and S1 have been loaded into the GHASH state registers previsously.
        gf_mult_req = 2'b11;
        if (gf_mult_ack_pre[0]) begin
          corr0_en_d = 1'b1;
        end
        if (gf_mult_ack_pre[1]) begin
          gf_mult1_in_sel_d = MULT_IN_ZERO;
        end
        if (&gf_mult_ack) begin
          gf_mult0_en_d     = 1'b0;
          gf_mult1_in_sel_d = MULT_IN_ZERO;
          corr_we           = SP2V_HIGH;
          aes_ghash_ns      = GHASH_IDLE;
        end
      end

      GHASH_MASKED_ADD_STATE_SHARES: begin
        // Add both shares of the GHASH state and store the result in Share 0.
        ghash_state_sel     = GHASH_STATE_ADD;
        ghash_state_we[0]   = SP2V_HIGH;
        final_add_d         = 1'b0;

        // Switch the add_in multiplexers back to the default position in the next clock cycle.
        ghash_add_in_sel_d[0] = ADD_IN_GHASH_IN;
        ghash_add_in_sel_d[1] = ADD_IN_GHASH_IN;

        if ((gcm_phase_i == GCM_SAVE) || ((gcm_phase_i == GCM_TAG) && final_add_q)) begin
          // When saving the context or when producing the final authentication tag, we have to
          // add Share 1 of S next and output the result.
          add_s_en_d   = 1'b1;
          aes_ghash_ns = GHASH_OUT;
        end else begin

          // Multiply Share 0 of the GHASH state with the hash subkey next. Share 1 of the GHASH
          // state is only multiplied by Share 1 of the hash subkey for the very first block.
          gf_mult0_en_d     = 1'b1;
          gf_mult1_in_sel_d = MULT_IN_STATE0;
          aes_ghash_ns      = GHASH_MULT;
        end
      end

      GHASH_MULT: begin
        // Perform the multiplication and update the state.
        gf_mult_req     = 2'b11;
        if (gf_mult_ack_pre[1]) begin
          gf_mult1_in_sel_d = MULT_IN_ZERO;
        end
        if (&gf_mult_ack) begin
          // Note: Once the multiplication finishes, Share 0 of the state depends on Share 0 of the
          // hash subkey. Thus, we don't forward it to the second multiplier as this may lead to
          // undesirable SCA leakage inside the multiplier.
          // When doing the first block only, we have to start computing another correction term
          // using the second multiplier in the next clock cycle, i.e., S1 * H1.
          gf_mult0_en_d     = 1'b0;
          gf_mult1_in_sel_d = SecMasking && first_block_q ? MULT_IN_S1 : MULT_IN_ZERO;

          ghash_state_sel   = GHASH_STATE_MULT;
          ghash_state_we[0] = SP2V_HIGH;
          ghash_state_we[1] = SP2V_HIGH;
          if (SecMasking) begin
            ghash_add_in_sel_d[0] = ADD_IN_CORR_A;
            ghash_add_in_sel_d[1] = first_block_q ? ADD_IN_GHASH_IN : ADD_IN_CORR_A;
            aes_ghash_ns          = GHASH_MASKED_ADD_CORR;
          end else begin
            first_block_d = 1'b0;
            aes_ghash_ns  = (gcm_phase_i == GCM_TAG) ? GHASH_OUT : GHASH_IDLE;
          end
        end
      end

      GHASH_MASKED_ADD_CORR: begin
        // Add the proper correction terms to both state shares.

        if (first_block_q) begin
          // When doing the first block only, we need to compute another correction term using the
          // second multiplier only, i.e., S1 * H1. To reduce undesirable SCA leakage, we should
          // not combine the previously computed correction term S0 * H1 with Share 1 of the GHASH
          // state or potential intermediate results of the second multiplier (both may depend on
          // S1). Only the final result of the second multiplier is forwarded to the addition.
          gf_mult_req = 2'b10;
          if (gf_mult_ack_pre[1]) begin
            ghash_add_in_sel_d[1] = ADD_IN_CORR_B;
            gf_mult1_in_sel_d     = MULT_IN_ZERO;
          end
          if (gf_mult_ack[1]) begin
            gf_mult1_in_sel_d = MULT_IN_ZERO;
            ghash_state_we[0] = SP2V_HIGH;
            ghash_state_we[1] = SP2V_HIGH;
            first_block_d     = 1'b0;
            advance           = 1'b1;
          end
        end else begin
          // We don't have to do another multiplication.
          advance = 1'b1;

          // Add the previously computed correction terms.
          ghash_state_we[0] = SP2V_HIGH;
          ghash_state_we[1] = SP2V_HIGH;
        end

        if (advance) begin
          if (gcm_phase_i == GCM_TAG) begin
            // When producing the final authentication tag, we have to unmask the state next.
            //
            // But before doing that, we pause for one clock cycle to allow downstream wires of the
            // GHASH state to fully settle to the corrected values. Otherwise, transient effects
            // inside the addition for Share 0 of the GHASH state may cause undesirable SCA
            // leakage. This is because before adding the correction terms, Share 0 and Share 1
            // of the GHASH state depends on H0 and H1, respectively.
            aes_ghash_ns = GHASH_MASKED_SETTLE;
          end else begin
            ghash_add_in_sel_d[0] = ADD_IN_GHASH_IN;
            ghash_add_in_sel_d[1] = ADD_IN_GHASH_IN;
            aes_ghash_ns          = GHASH_IDLE;
          end
        end
      end

      GHASH_MASKED_SETTLE: begin
        // After adding the correction terms the last time and before unmasking the state, we pause
        // for one clock cycle. This allows downstream wires of the GHASH state to fully settle to
        // the corrected values to reduce undesirable SCA leakage.
        final_add_d           = 1'b1;
        ghash_add_in_sel_d[0] = ADD_IN_CORR_B;
        ghash_add_in_sel_d[1] = ADD_IN_GHASH_IN;
        aes_ghash_ns          = GHASH_MASKED_ADD_STATE_SHARES;
      end

      GHASH_ADD_S: begin
        // Add S to the GHASH state and then return to the idle state. This state is used for the
        // unmasked implementation only. The generatiion of the final authentication tag (also
        // involves adding the GHASH state and S) is handled separately in the GHASH_OUT FSM state.
        ghash_state_sel   = GHASH_STATE_ADD_S;
        ghash_state_we[0] = SP2V_HIGH;
        aes_ghash_ns      = GHASH_IDLE;
      end

      GHASH_OUT: begin
        // Add S to the GHASH state to output the final authentication tag. Upon performing the
        // output handshake, clear all internal state with pseudo-random data.
        add_s_en_d  = 1'b1;
        out_valid_o = SP2V_HIGH;
        if (out_ready_i == SP2V_HIGH) begin
          add_s_en_d        = 1'b0;
          s_we              = SP2V_HIGH;
          ghash_state_sel   = SecMasking ? GHASH_STATE_INIT : GHASH_STATE_ADD;
          ghash_state_we[0] = SP2V_HIGH;
          ghash_state_we[1] = SP2V_HIGH;
          hash_subkey_we    = SP2V_HIGH;
          aes_ghash_ns      = SecMasking ? GHASH_MASKED_INIT : GHASH_IDLE;
        end
      end

      GHASH_ERROR: begin
        // Terminal error state
        alert_o = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious glitch), error out immediately.
      default: begin
        aes_ghash_ns = GHASH_ERROR;
        alert_o = 1'b1;
      end
    endcase

    // Unconditionally jump into the terminal error state in case a mux selector becomes invalid,
    // or if a fatal alert has been triggered.
    if (|ghash_add_in_sel_err || gf_mult1_in_sel_err || alert_fatal_i) begin
      aes_ghash_ns = GHASH_ERROR;
    end
  end

  // SEC_CM: GHASH.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, aes_ghash_ns,
      aes_ghash_cs, aes_ghash_e, GHASH_IDLE)

  always_ff @(posedge clk_i or negedge rst_ni) begin : fsm_reg
    if (!rst_ni) begin
      first_block_q <= 1'b0;
    end else begin
      first_block_q <= first_block_d;
    end
  end

  if (SecMasking) begin : gen_fsm_reg_masked
    always_ff @(posedge clk_i or negedge rst_ni) begin : fsm_reg_masked
      if (!rst_ni) begin
        final_add_q <= 1'b0;
      end else begin
        final_add_q <= final_add_d;
      end
    end

  end else begin : gen_no_fsm_reg
    // Tie-off unused FSM signals.
    logic unused_final_add_d;
    assign final_add_q = 1'b0;
    assign unused_final_add_d = final_add_d;

    logic unused_gf_mult0_en_d;
    assign gf_mult0_en_q = 1'b0;
    assign unused_gf_mult0_en_d = gf_mult0_en_d;

    gf_mult_in_sel_e unused_gf_mult1_in_sel_d;
    assign gf_mult1_in_sel_q = MULT_IN_ZERO;
    assign unused_gf_mult1_in_sel_d = gf_mult1_in_sel_d;

    logic unused_advance;
    assign unused_advance = advance;
  end

  /////////////
  // Outputs //
  /////////////

  // Moving to GCM_SAVE is only allowed after having done the first block.
  assign first_block_o = first_block_q;

  // Add S to the GHASH state for the generation of the final authentication tag. To reduce
  // undesirable SCA leakage, the following measures are taken:
  // 1. A blanker is used to only perform the addition at the very end. This avoids adding
  //    S to intermediate GHASH states. This is done for the masked implementation only.
  // 2. The result of the addition is not written back into state regsiter but forwarded to
  //    the output directly.
  if (SecMasking) begin : gen_add_s_in_masked
    // Avoid glichtes on the enable signal controlling the blanking.
    prim_flop #(
      .Width     (1),
      .ResetValue(1'b0)
    ) u_prim_flop_add_s_en (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .d_i(add_s_en_d),
      .q_o(add_s_en_q)
    );

    // Only feed Share 0 of the GHASH state into the addition if we're actually generating and
    // output. This helps reducing undesirable SCA leakage due to combining intermediate values of
    // Share 0 of the GHASH state with Share 1 of S.
    prim_blanker #(
      .Width(GCMDegree)
    ) u_prim_blanker_add_s_in (
      .in_i (ghash_state_q[0]),
      .en_i (add_s_en_q),
      .out_o(add_s_in)
    );
  end else begin : gen_add_s_in_unmasked

    // Don't perform any blanking in the unmasked case.
    assign add_s_in = ghash_state_q[0];
  end

  // Perform the actual addition.
  assign ghash_state_done = s_q ^ add_s_in;

  // Covert the output data from the internal data format to the output format.
  always_comb begin : data_out_conversion
    ghash_state_done_o = aes_transpose(aes_state_to_ghash_vec(ghash_state_done));
  end

endmodule
