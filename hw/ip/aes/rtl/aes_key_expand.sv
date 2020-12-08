// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES KeyExpand

`include "prim_assert.sv"

module aes_key_expand import aes_pkg::*;
#(
  parameter bit         AES192Enable = 1,
  parameter bit         Masking      = 0,
  parameter sbox_impl_e SBoxImpl     = SBoxImplLut,

  localparam int        NumShares    = Masking ? 2 : 1 // derived parameter
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,
  input  logic                   cfg_valid_i,
  input  ciph_op_e               op_i,
  input  logic                   en_i,
  output logic                   out_req_o,
  input  logic                   out_ack_i,
  input  logic                   clear_i,
  input  logic             [3:0] round_i,
  input  key_len_e               key_len_i,
  input  logic       [7:0][31:0] key_i [NumShares],
  output logic       [7:0][31:0] key_o [NumShares],
  input  logic [WidthPRDKey-1:0] prd_masking_i
);

  logic                [7:0] rcon_d, rcon_q;
  logic                      rcon_we;
  logic                      use_rcon;

  logic                [3:0] rnd;
  logic                [3:0] rnd_type;

  logic               [31:0] spec_in_128 [NumShares];
  logic               [31:0] spec_in_192 [NumShares];
  logic               [31:0] rot_word_in [NumShares];
  logic               [31:0] rot_word_out [NumShares];
  logic                      use_rot_word;
  logic               [31:0] sub_word_in, sub_word_out;
  logic                [3:0] sub_word_out_req;
  logic               [31:0] sw_in_mask, sw_out_mask;
  logic [4*WidthPRDSBox-1:0] sw_prd;
  logic                [7:0] rcon_add_in, rcon_add_out;
  logic               [31:0] rcon_added;

  logic               [31:0] irregular [NumShares];
  logic          [7:0][31:0] regular [NumShares];

  // cfg_valid_i is used for gating assertions only.
  logic                      unused_cfg_valid;
  assign unused_cfg_valid = cfg_valid_i;

  // Get a shorter reference.
  assign rnd = round_i;

  // For AES-192, there are four different types of rounds.
  always_comb begin : get_rnd_type
    if (AES192Enable) begin
      rnd_type[0] = (rnd == 0);
      rnd_type[1] = (rnd == 1 || rnd == 4 || rnd == 7 || rnd == 10);
      rnd_type[2] = (rnd == 2 || rnd == 5 || rnd == 8 || rnd == 11);
      rnd_type[3] = (rnd == 3 || rnd == 6 || rnd == 9 || rnd == 12);
    end else begin
      rnd_type = '0;
    end
  end

  //////////////////////////////////////////////////////
  // Irregular part involving Rcon, RotWord & SubWord //
  //////////////////////////////////////////////////////

  // Depending on key length and round, RotWord may not be used.
  assign use_rot_word = (key_len_i == AES_256 && rnd[0] == 1'b0) ? 1'b0 : 1'b1;

  // Depending on operation, key length and round, Rcon may not be used thus must not be updated.
  always_comb begin : rcon_usage
    use_rcon = 1'b1;

    if (AES192Enable) begin
      if (key_len_i == AES_192 &&
          ((op_i == CIPH_FWD &&  rnd_type[1]) ||
           (op_i == CIPH_INV && (rnd_type[0] || rnd_type[3])))) begin
        use_rcon = 1'b0;
      end
    end

    if (key_len_i == AES_256 && rnd[0] == 1'b0) begin
      use_rcon = 1'b0;
    end
  end

  // Generate Rcon
  always_comb begin : rcon_update
    rcon_d = rcon_q;

    if (clear_i) begin
      rcon_d = (op_i == CIPH_FWD)                            ? 8'h01 :
              ((op_i == CIPH_INV) && (key_len_i == AES_128)) ? 8'h36 :
              ((op_i == CIPH_INV) && (key_len_i == AES_192)) ? 8'h80 :
              ((op_i == CIPH_INV) && (key_len_i == AES_256)) ? 8'h40 : 8'h01;
    end else begin
      rcon_d = (op_i == CIPH_FWD) ? aes_mul2(rcon_q) :
               (op_i == CIPH_INV) ? aes_div2(rcon_q) : 8'h01;
    end
  end

  // Advance.
  assign rcon_we = clear_i | (en_i & out_req_o & out_ack_i & use_rcon);

  // Rcon register
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_rcon
    if (!rst_ni) begin
      rcon_q <= '0;
    end else if (rcon_we) begin
      rcon_q <= rcon_d;
    end
  end

  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_rot_word_out
    // Special input, equivalent to key_o[3] in the used cases
    assign spec_in_128[s] = key_i[s][3] ^ key_i[s][2];
    assign spec_in_192[s] = AES192Enable ? key_i[s][5] ^ key_i[s][1] ^ key_i[s][0] : '0;

    // Select input
    always_comb begin : rot_word_in_mux
      unique case (key_len_i)

        /////////////
        // AES-128 //
        /////////////
        AES_128: begin
          unique case (op_i)
            CIPH_FWD: rot_word_in[s] = key_i[s][3];
            CIPH_INV: rot_word_in[s] = spec_in_128[s];
            default:  rot_word_in[s] = key_i[s][3];
          endcase
        end

        /////////////
        // AES-192 //
        /////////////
        AES_192: begin
          if (AES192Enable) begin
            unique case (op_i)
              CIPH_FWD: begin
                rot_word_in[s] = rnd_type[0] ? key_i[s][5]    :
                                 rnd_type[2] ? key_i[s][5]    :
                                 rnd_type[3] ? spec_in_192[s] : key_i[s][3];
              end
              CIPH_INV: begin
                rot_word_in[s] = rnd_type[1] ? key_i[s][3] :
                                 rnd_type[2] ? key_i[s][1] : key_i[s][3];
              end
              default: rot_word_in[s] = key_i[s][3];
            endcase
          end else begin
            rot_word_in[s] = key_i[s][3];
          end
        end

        /////////////
        // AES-256 //
        /////////////
        AES_256: begin
          unique case (op_i)
            CIPH_FWD: rot_word_in[s] = key_i[s][7];
            CIPH_INV: rot_word_in[s] = key_i[s][3];
            default:  rot_word_in[s] = key_i[s][7];
          endcase
        end

        default: rot_word_in[s] = key_i[s][3];
      endcase
    end

    // RotWord: cyclic byte shift
    assign rot_word_out[s] = aes_circ_byte_shift(rot_word_in[s], 2'h3);
  end

  // Mux input for SubWord
  assign sub_word_in = use_rot_word ? rot_word_out[0] : rot_word_in[0];

  // Masking
  if (!Masking) begin : gen_no_sw_in_mask
    // The mask share is ignored anyway, it can be 0.
    assign sw_in_mask  = '0;
  end else begin : gen_sw_in_mask
    // The input mask is the mask share of rot_word_in/out.
    assign sw_in_mask = use_rot_word ? rot_word_out[1] : rot_word_in[1];
  end

  assign sw_out_mask = aes_sb_out_mask_get(prd_masking_i);
  assign sw_prd      = aes_sb_prd_get(prd_masking_i);

  // SubWord - individually substitute bytes.
  for (genvar i = 0; i < 4; i++) begin : gen_sbox
    aes_sbox #(
      .SBoxImpl ( SBoxImpl )
    ) u_aes_sbox_i (
      .clk_i         ( clk_i                                  ),
      .rst_ni        ( rst_ni                                 ),
      .en_i          ( en_i                                   ),
      .out_req_o     ( sub_word_out_req[i]                    ),
      .out_ack_i     ( out_ack_i                              ),
      .op_i          ( CIPH_FWD                               ),
      .data_i        ( sub_word_in[8*i +: 8]                  ),
      .in_mask_i     ( sw_in_mask[8*i +: 8]                   ),
      .out_mask_i    ( sw_out_mask[8*i +: 8]                  ),
      .prd_masking_i ( sw_prd[WidthPRDSBox*i +: WidthPRDSBox] ),
      .data_o        ( sub_word_out[8*i +: 8]                 )
    );
  end

  // Add Rcon
  assign rcon_add_in  = sub_word_out[7:0];
  assign rcon_add_out = rcon_add_in ^ rcon_q;
  assign rcon_added   = {sub_word_out[31:8], rcon_add_out};

  // Mux output coming from Rcon & SubWord
  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_irregular
    if (s == 0) begin : gen_irregular_rcon
      // The (masked) key share
      assign irregular[s] = use_rcon ? rcon_added : sub_word_out;
    end else begin : gen_irregular_no_rcon
      // The mask share
      assign irregular[s] = sw_out_mask;
    end
  end

  ///////////////////////////
  // The more regular part //
  ///////////////////////////

  // To reduce muxing resources, we re-use existing
  // connections for unused words and default cases.
  for (genvar s = 0; s < NumShares; s++) begin : gen_shares_regular
    always_comb begin : drive_regular
      unique case (key_len_i)

        /////////////
        // AES-128 //
        /////////////
        AES_128: begin
          // key_o[7:4] not used
          regular[s][7:4] = key_i[s][3:0];

          regular[s][0] = irregular[s] ^ key_i[s][0];
          unique case (op_i)
            CIPH_FWD: begin
              for (int i=1; i<4; i++) begin
                regular[s][i] = regular[s][i-1] ^ key_i[s][i];
              end
            end

            CIPH_INV: begin
              for (int i=1; i<4; i++) begin
                regular[s][i] = key_i[s][i-1] ^ key_i[s][i];
              end
            end

            default: regular[s] = {key_i[s][3:0], key_i[s][7:4]};
          endcase
        end

        /////////////
        // AES-192 //
        /////////////
        AES_192: begin
          // key_o[7:6] not used
          regular[s][7:6] = key_i[s][3:2];

          if (AES192Enable) begin
            unique case (op_i)
              CIPH_FWD: begin
                if (rnd_type[0]) begin
                  // Shift down four upper most words
                  regular[s][3:0] = key_i[s][5:2];
                  // Generate Words 6 and 7
                  regular[s][4]   = irregular[s]  ^ key_i[s][0];
                  regular[s][5]   = regular[s][4] ^ key_i[s][1];
                end else begin
                  // Shift down two upper most words
                  regular[s][1:0] = key_i[s][5:4];
                  // Generate new upper four words
                  for (int i=0; i<4; i++) begin
                    if ((i == 0 && rnd_type[2]) ||
                        (i == 2 && rnd_type[3])) begin
                      regular[s][i+2] = irregular[s]    ^ key_i[s][i];
                    end else begin
                      regular[s][i+2] = regular[s][i+1] ^ key_i[s][i];
                    end
                  end
                end // rnd_type[0]
              end

              CIPH_INV: begin
                if (rnd_type[0]) begin
                  // Shift up four lowest words
                  regular[s][5:2] = key_i[s][3:0];
                  // Generate Word 44 and 45
                  for (int i=0; i<2; i++) begin
                    regular[s][i] = key_i[s][3+i] ^ key_i[s][3+i+1];
                  end
                end else begin
                  // Shift up two lowest words
                  regular[s][5:4] = key_i[s][1:0];
                  // Generate new lower four words
                  for (int i=0; i<4; i++) begin
                    if ((i == 2 && rnd_type[1]) ||
                        (i == 0 && rnd_type[2])) begin
                      regular[s][i] = irregular[s]  ^ key_i[s][i+2];
                    end else begin
                      regular[s][i] = key_i[s][i+1] ^ key_i[s][i+2];
                    end
                  end
                end // rnd_type[0]
              end

              default: regular[s] = {key_i[s][3:0], key_i[s][7:4]};
            endcase

          end else begin
            regular[s] = {key_i[s][3:0], key_i[s][7:4]};
          end // AES192Enable
        end

        /////////////
        // AES-256 //
        /////////////
        AES_256: begin
          unique case (op_i)
            CIPH_FWD: begin
              if (rnd == 0) begin
                // Round 0: Nothing to be done
                // The Full Key registers are not updated
                regular[s] = {key_i[s][3:0], key_i[s][7:4]};
              end else begin
                // Shift down old upper half
                regular[s][3:0] = key_i[s][7:4];
                // Generate new upper half
                regular[s][4]   = irregular[s] ^ key_i[s][0];
                for (int i=1; i<4; i++) begin
                  regular[s][i+4] = regular[s][i+4-1] ^ key_i[s][i];
                end
              end // rnd == 0
            end

            CIPH_INV: begin
              if (rnd == 0) begin
                // Round 0: Nothing to be done
                // The Full Key registers are not updated
                regular[s] = {key_i[s][3:0], key_i[s][7:4]};
              end else begin
                // Shift up old lower half
                regular[s][7:4] = key_i[s][3:0];
                // Generate new lower half
                regular[s][0]   = irregular[s] ^ key_i[s][4];
                for (int i=0; i<3; i++) begin
                  regular[s][i+1] = key_i[s][4+i] ^ key_i[s][4+i+1];
                end
              end // rnd == 0
            end

            default: regular[s] = {key_i[s][3:0], key_i[s][7:4]};
          endcase
        end

        default: regular[s] = {key_i[s][3:0], key_i[s][7:4]};
      endcase // key_len_i
    end // drive_regular
  end // gen_shares_regular

  // Drive output
  assign key_o     = regular;
  assign out_req_o = &sub_word_out_req;

  ////////////////
  // Assertions //
  ////////////////

  // Cipher core masking requires a masked SBox and vice versa.
  `ASSERT_INIT(AesMaskedCoreAndSBox,
      (Masking &&
      (SBoxImpl == SBoxImplCanrightMasked ||
       SBoxImpl == SBoxImplCanrightMaskedNoreuse)) ||
      (!Masking &&
      (SBoxImpl == SBoxImplLut ||
       SBoxImpl == SBoxImplCanright)))

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesCiphOpKnown, op_i)
  `ASSERT(AesKeyLenValid, cfg_valid_i |-> key_len_i inside {
      AES_128,
      AES_192,
      AES_256
      })

  // Make sure the output of the masking PRNG is properly extracted without creating overlaps
  // of masks and PRD distributed to the individual S-Boxes.
  logic [WidthPRDKey-1:0] unused_prd_masking;
  assign unused_prd_masking = aes_sb_out_mask_prd_concat(sw_out_mask, sw_prd);
  `ASSERT(AesMskgPrdExtraction, prd_masking_i == unused_prd_masking)

endmodule
