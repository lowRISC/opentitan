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
  parameter bit         SecMasking   = 1,
  parameter sbox_impl_e SecSBoxImpl  = SBoxImplDom,

  localparam int        NumShares    = SecMasking ? 2 : 1 // derived parameter
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
  input  logic                         alert_fatal_i,
  output logic                         alert_o,

  // I/O data signals
  input  logic         [3:0][3:0][7:0] cipher_state_init_i [NumShares], // Masked cipher core input
                                                                        // for GCM_RESTORE
  input  logic         [GCMDegree-1:0] data_in_prev_i,                  // Ciphertext for decryption
                                                                        // or AAD
  input  logic [NumRegsData-1:0][31:0] data_out_i,                      // Ciphertext for encryption
  input  logic         [3:0][3:0][7:0] cipher_state_done_i [NumShares], // Masked cipher core output
  output logic [NumRegsData-1:0][31:0] ghash_state_done_o
);

  // Parameters
  // The number of cycles must be a power of two and ideally matches the minimum latency of the
  // cipher core which is 56 clock cycles (masked) or 12 clock cycles (unmasked) for AES-128.
  localparam int unsigned GFMultCycles = (SecSBoxImpl == SBoxImplDom) ? 32 : 8;

  // Signals
  logic [GCMDegree-1:0] s_d;
  logic [GCMDegree-1:0] s_q;
  sp2v_e                s_we;
  logic [GCMDegree-1:0] corr_d [2];
  logic [GCMDegree-1:0] corr_q [2];
  sp2v_e                corr_we;
  logic [15:0][7:0]     ghash_in;
  logic [15:0][7:0]     ghash_in_valid;
  ghash_in_sel_e        ghash_in_sel;
  ghash_add_in_sel_e    ghash_add_in_sel [2];
  logic [GCMDegree-1:0] ghash_state_d [NumShares];
  logic [GCMDegree-1:0] ghash_state_q [NumShares];
  logic [GCMDegree-1:0] ghash_state_add [NumShares];
  sp2v_e                ghash_state_we [2];
  ghash_state_sel_e     ghash_state_sel;
  logic [GCMDegree-1:0] ghash_state_mult [NumShares];
  logic [GCMDegree-1:0] hash_subkey_d [NumShares];
  logic [GCMDegree-1:0] hash_subkey_q [NumShares];
  sp2v_e                hash_subkey_we;
  gf_mult_in_sel_e      gf_mult1_in_sel;
  logic [1:0]           gf_mult_req;
  logic [1:0]           gf_mult_ack;
  aes_ghash_e           aes_ghash_ns, aes_ghash_cs;
  logic                 first_block_d;
  logic                 first_block_q;
  logic                 final_add_d;
  logic                 final_add_q;

  //////////////////////////////////
  // Input Data Format Conversion //
  //////////////////////////////////
  // Covert the input data to the internal data format.
  logic [GCMDegree-1:0] cipher_state_init [NumShares];
  logic [GCMDegree-1:0] cipher_state_done [NumShares];
  logic [GCMDegree-1:0] data_in_prev;
  logic [GCMDegree-1:0] data_out;
  always_comb begin : data_in_conversion
    for (int s = 0; s < NumShares; s++) begin
      cipher_state_done[s] = aes_state_to_ghash_vec(cipher_state_done_i[s]);
      cipher_state_init[s] = aes_state_to_ghash_vec(cipher_state_init_i[s]);
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
  // These register can be cleared after pushing some pseudo-random data through the multipliers.
  if (SecMasking) begin : gen_corr_terms
    assign corr_d[0] = ghash_state_mult[0] ^ ghash_state_q[0];
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
  // Select the ciphertext for encryption / decryption or S for the final authentication tag.
  always_comb begin : ghash_in_mux
    unique case (ghash_in_sel)
      GHASH_IN_DATA_IN_PREV: ghash_in = data_in_prev;
      GHASH_IN_DATA_OUT:     ghash_in = data_out;
      GHASH_IN_S:            ghash_in = s_q;
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
    // term to the GHASH state. The selection may vary between the two shares.
    always_comb begin : add_in_mux0
      unique case (ghash_add_in_sel[0])
        ADD_IN_GHASH_IN: add_in[0] = ghash_in_valid;
        ADD_IN_CORR_A:   add_in[0] = corr_q[0];
        ADD_IN_CORR_B:   add_in[0] = ghash_state_q[1];
        default:         add_in[0] = ghash_in_valid;
      endcase
    end

    always_comb begin : add_in_mux1
      unique case (ghash_add_in_sel[1])
        ADD_IN_GHASH_IN: add_in[1] = ghash_in_valid;
        ADD_IN_CORR_A:   add_in[1] = corr_q[1];
        ADD_IN_CORR_B:   add_in[1] = ghash_state_mult[1];
        default:         add_in[1] = ghash_in_valid;
      endcase
    end

    // Perform the addition on a per-share basis.
    for (genvar s = 0; s < NumShares; s++) begin : gen_state_add
      assign ghash_state_add[s] = ghash_state_q[s] ^ add_in[s];
    end

  end else begin : gen_unmasked_add

    // Simply add the GHASH input to the current state.
    assign ghash_state_add[0] = ghash_state_q[0] ^ ghash_in_valid;
  end

  // We initialize the state with S (masked implementation) or with zero (unmasked implementation).
  always_comb begin : ghash_state_mux
    unique case (ghash_state_sel)
      GHASH_STATE_RESTORE: ghash_state_d = cipher_state_init;
      GHASH_STATE_INIT:    ghash_state_d = SecMasking ? cipher_state_done : '{default: '0};
      GHASH_STATE_ADD:     ghash_state_d = ghash_state_add;
      GHASH_STATE_MULT:    ghash_state_d = ghash_state_mult;
      default:             ghash_state_d = ghash_state_add;
    endcase
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
  logic [GCMDegree-1:0] gf_mult_op_a[NumShares];
  logic [GCMDegree-1:0] gf_mult_prod[NumShares];

  // The first multiplier has no muxes on the operand inputs.
  assign gf_mult_op_a[0] = ghash_state_q[0];

  if (SecMasking) begin : gen_gf_mult_s1_mux
    // The second multiplier is used to multiply Share 0, Share 1 (first block only) of
    // the state, and also Share 1 of S with Share 1 of the hash subkey.
    always_comb begin : gf_mult1_in_mux
      unique case (gf_mult1_in_sel)
        MULT_IN_STATE0:  gf_mult_op_a[1] = ghash_state_q[0];
        MULT_IN_STATE1:  gf_mult_op_a[1] = ghash_state_q[1];
        MULT_IN_S1:      gf_mult_op_a[1] = s_q;
        default:         gf_mult_op_a[1] = ghash_state_q[0];
      endcase
    end
  end

  for (genvar s = 0; s < NumShares; s++) begin : gen_gf_mult
    prim_gf_mult #(
      .Width         (GCMDegree),
      .StagesPerCycle(GCMDegree / GFMultCycles),
      .IPoly         (GCMIPoly)
    ) u_gf_mult (
      .clk_i (clk_i),
      .rst_ni(rst_ni),

      .req_i(gf_mult_req[s]),
      .ack_o(gf_mult_ack[s]),

      .operand_a_i(aes_ghash_reverse_bit_order(gf_mult_op_a[s])),  // The A input is scanned.
      .operand_b_i(aes_ghash_reverse_bit_order(hash_subkey_q[s])), // The B input is not scanned.

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

    logic unused_ghash_add_in_sel;
    assign unused_ghash_add_in_sel = ^{{ghash_add_in_sel[0]}, {ghash_add_in_sel[1]}};

    sp2v_e unused_ghash_state_we;
    assign unused_ghash_state_we = ghash_state_we[1];

    gf_mult_in_sel_e unused_gf_mult1_in_sel;
    assign unused_gf_mult1_in_sel = gf_mult1_in_sel;

    logic unused_gf_mult_req;
    assign unused_gf_mult_req = gf_mult_req[1];
    assign gf_mult_ack[1]     = 1'b1;
  end

  /////////////////
  // Control FSM //
  /////////////////

  always_comb begin : aes_ghash_fsm

    // Handshake signals
    in_ready_o  = SP2V_LOW;
    out_valid_o = SP2V_LOW;

    // Data path
    s_we    = SP2V_LOW;
    corr_we = SP2V_LOW;

    ghash_in_sel = GHASH_IN_DATA_OUT;

    ghash_add_in_sel[0] = ADD_IN_GHASH_IN;
    ghash_add_in_sel[1] = ADD_IN_GHASH_IN;

    ghash_state_sel   = GHASH_STATE_ADD;
    ghash_state_we[0] = SP2V_LOW;
    ghash_state_we[1] = SP2V_LOW;

    hash_subkey_we = SP2V_LOW;

    gf_mult1_in_sel = MULT_IN_STATE0;
    gf_mult_req     = '0;

    // FSM
    aes_ghash_ns  = aes_ghash_cs;
    first_block_d = first_block_q;
    final_add_d   = final_add_q;

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
            aes_ghash_ns = SecMasking ? GHASH_MASKED_INIT : aes_ghash_cs;

          end else if (gcm_phase_i == GCM_INIT) begin
            if (load_hash_subkey_i == SP2V_HIGH) begin

              // Load the hash subkey.
              hash_subkey_we  = SP2V_HIGH;
            end else begin

              // Load S and initialize the state (with S in case of the masked implementation).
              s_we              = SP2V_HIGH;
              ghash_state_sel   = GHASH_STATE_INIT;
              ghash_state_we[0] = SP2V_HIGH;
              ghash_state_we[1] = SP2V_HIGH;

              // We have now all pre-requisites to compute the correction terms for the masked
              // implementation.
              aes_ghash_ns = SecMasking ? GHASH_MASKED_INIT : GHASH_IDLE;
            end

          end else if (gcm_phase_i == GCM_RESTORE) begin
            // Restore a previously loaded GHASH state.
            ghash_state_sel   = GHASH_STATE_RESTORE;
            ghash_state_we[0] = SP2V_HIGH;
            ghash_state_we[1] = SP2V_HIGH;
            first_block_d     = 1'b0;

            // For the masked implementation, we have to again substract Share 1 of S. It is only
            // added at the very end (or when saving the GHASH state).
            aes_ghash_ns = SecMasking ? GHASH_ADD_S : GHASH_IDLE;

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

            // Start the multiplication. In case masking is enabled and we've already done the
            // first block, we have to do one more addtion first.
            aes_ghash_ns =
                SecMasking && !first_block_q ? GHASH_MASKED_ADD_STATE_SHARES : GHASH_MULT;

          end else if (gcm_phase_i == GCM_SAVE) begin
            // Get ready to output the current GHASH state.

            // For the masked implementation, first add Share 1 and then unmask the GHASH state.
            ghash_in_sel      = SecMasking ? GHASH_IN_S : GHASH_IN_DATA_OUT;
            ghash_state_we[0] = SecMasking ? SP2V_HIGH  : SP2V_LOW;
            final_add_d       = 1'b1;
            aes_ghash_ns      = SecMasking ? GHASH_MASKED_ADD_STATE_SHARES : GHASH_OUT;

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
        gf_mult1_in_sel = MULT_IN_STATE0;
        gf_mult_req     = 2'b11;
        if (&gf_mult_ack) begin
          corr_we       = SP2V_HIGH;
          aes_ghash_ns  = GHASH_IDLE;
          first_block_d = 1'b1;
        end
      end

      GHASH_MASKED_ADD_STATE_SHARES: begin
        // Add both shares of the GHASH state and store the result in Share 0.
        ghash_add_in_sel[0] = ADD_IN_CORR_B;
        ghash_state_sel     = GHASH_STATE_ADD;
        ghash_state_we[0]   = SP2V_HIGH;
        final_add_d         = 1'b0;
        aes_ghash_ns        = ((gcm_phase_i == GCM_SAVE) ||
                               (gcm_phase_i == GCM_TAG)) && final_add_q ? GHASH_OUT : GHASH_MULT;
      end

      GHASH_MULT: begin
        // Perform the multiplication and update the state.
        gf_mult1_in_sel = first_block_q ? MULT_IN_STATE1 : MULT_IN_STATE0;
        gf_mult_req     = 2'b11;
        if (&gf_mult_ack) begin
          ghash_state_sel   = GHASH_STATE_MULT;
          ghash_state_we[0] = SP2V_HIGH;
          ghash_state_we[1] = SP2V_HIGH;
          aes_ghash_ns      = SecMasking               ? GHASH_MASKED_ADD_CORR :
                              (gcm_phase_i == GCM_TAG) ? GHASH_ADD_S           : GHASH_IDLE;
        end
      end

      GHASH_MASKED_ADD_CORR: begin
        // Add the proper correction terms to both state shares.
        ghash_add_in_sel[0] = ADD_IN_CORR_A;
        ghash_add_in_sel[1] = ADD_IN_CORR_A;

        if (first_block_q) begin
          // When doing the first block only, we need to compute another correction term using the
          // second multiplier only, i.e., S1 * H1.
          ghash_add_in_sel[1] = ADD_IN_CORR_B;
          gf_mult1_in_sel     = MULT_IN_S1;
          gf_mult_req[1]      = 1'b1;
          if (gf_mult_ack[1]) begin
            ghash_state_we[0] = SP2V_HIGH;
            ghash_state_we[1] = SP2V_HIGH;
            first_block_d     = 1'b0;
            aes_ghash_ns      = (gcm_phase_i == GCM_TAG) ? GHASH_ADD_S : GHASH_IDLE;
          end
        end else begin
          // We don't have to do another multiplication.
          ghash_state_we[0] = SP2V_HIGH;
          ghash_state_we[1] = SP2V_HIGH;
          aes_ghash_ns      = (gcm_phase_i == GCM_TAG) ? GHASH_ADD_S : GHASH_IDLE;
        end
      end

      GHASH_ADD_S: begin
        // Add S to the GHASH state and then get ready to output the final tag.
        ghash_in_sel      = GHASH_IN_S;
        ghash_state_we[0] = SP2V_HIGH;

        // When restoring a previously saved GHASH state in the masked implementation, Share 1 of S
        // must be subtracted from the restored GHASH state before further blocks can be processed.
        // It is added again at the very end. In case of the masked implementation, we have to
        // unmask the GHASH state and can then output the final tag.
        final_add_d  = gcm_phase_i != GCM_RESTORE;
        aes_ghash_ns =
            SecMasking && (gcm_phase_i == GCM_RESTORE) ? GHASH_IDLE                    :
            SecMasking                                 ? GHASH_MASKED_ADD_STATE_SHARES : GHASH_OUT;
      end

      GHASH_OUT: begin
        // Perform output handshake and clear all internal state with pseudo-random data.
        out_valid_o = SP2V_HIGH;
        if (out_ready_i == SP2V_HIGH) begin
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

    // Unconditionally jump into the terminal error state if a fatal alert has been triggered.
    if (alert_fatal_i) begin
      aes_ghash_ns = GHASH_ERROR;
    end
  end

  // SEC_CM: GHASH.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, aes_ghash_ns,
      aes_ghash_cs, aes_ghash_e, GHASH_IDLE)

  if (SecMasking) begin : gen_fsm_reg
    always_ff @(posedge clk_i or negedge rst_ni) begin : fsm_reg
      if (!rst_ni) begin
        first_block_q <= 1'b0;
        final_add_q   <= 1'b0;
      end else begin
        first_block_q <= first_block_d;
        final_add_q   <= final_add_d;
      end
    end
  end else begin : gen_no_fsm_reg
    // Tie-off unused FSM signals.
    logic unused_first_block_d;
    logic unused_final_add_d;
    assign first_block_q = 1'b0;
    assign final_add_q   = 1'b0;
    assign unused_first_block_d = first_block_d;
    assign unused_final_add_d   = final_add_d;
  end

  /////////////
  // Outputs //
  /////////////

  // Covert the output data from the internal data format to the output format.
  always_comb begin : data_out_conversion
    ghash_state_done_o = aes_transpose(aes_state_to_ghash_vec(ghash_state_q[0]));
  end

endmodule
