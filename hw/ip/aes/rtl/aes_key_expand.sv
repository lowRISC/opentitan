// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES KeyExpand

`include "prim_assert.sv"

module aes_key_expand #(
  parameter bit AES192Enable = 1,
  parameter     SBoxImpl     = "lut"
) (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  aes_pkg::ciph_op_e op_i,
  input  logic              step_i,
  input  logic              clear_i,
  input  logic        [3:0] round_i,
  input  aes_pkg::key_len_e key_len_i,
  input  logic  [7:0][31:0] key_i,
  output logic  [7:0][31:0] key_o
);

  import aes_pkg::*;

  logic       [7:0] rcon_d, rcon_q;
  logic             rcon_we;
  logic             use_rcon;

  logic       [3:0] rnd;
  logic       [3:0] rnd_type;

  logic      [31:0] spec_in_128, spec_in_192;
  logic      [31:0] rot_word_in, rot_word_out;
  logic             use_rot_word;
  logic      [31:0] sub_word_in, sub_word_out;
  logic       [7:0] rcon_add_in, rcon_add_out;
  logic      [31:0] rcon_added;

  logic      [31:0] irregular;
  logic [7:0][31:0] regular;

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

  assign rcon_we = clear_i | (step_i & use_rcon);

  // Rcon register
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_rcon
    if (!rst_ni) begin
      rcon_q <= '0;
    end else if (rcon_we) begin
      rcon_q <= rcon_d;
    end
  end

  // Special input, equivalent to key_o[3] in the used cases
  assign spec_in_128 = key_i[3] ^ key_i[2];
  assign spec_in_192 = AES192Enable ? key_i[5] ^ key_i[1] ^ key_i[0] : '0;

  // Select input
  always_comb begin : rot_word_in_mux
    unique case (key_len_i)

      /////////////
      // AES-128 //
      /////////////
      AES_128: begin
        unique case (op_i)
          CIPH_FWD: rot_word_in = key_i[3];
          CIPH_INV: rot_word_in = spec_in_128;
          default:  rot_word_in = key_i[3];
        endcase
      end

      /////////////
      // AES-192 //
      /////////////
      AES_192: begin
        if (AES192Enable) begin
          unique case (op_i)
            CIPH_FWD: begin
              rot_word_in = rnd_type[0] ? key_i[5]    :
                            rnd_type[2] ? key_i[5]    :
                            rnd_type[3] ? spec_in_192 : key_i[3];
            end
            CIPH_INV: begin
              rot_word_in = rnd_type[1] ? key_i[3] :
                            rnd_type[2] ? key_i[1] : key_i[3];
            end
            default: rot_word_in = key_i[3];
          endcase
        end else begin
          rot_word_in = key_i[3];
        end
      end

      /////////////
      // AES-256 //
      /////////////
      AES_256: begin
        unique case (op_i)
          CIPH_FWD: rot_word_in = key_i[7];
          CIPH_INV: rot_word_in = key_i[3];
          default:  rot_word_in = key_i[7];
        endcase
      end

      default: rot_word_in = key_i[3];
    endcase
  end

  // RotWord: cyclic byte shift
  assign rot_word_out = aes_circ_byte_shift(rot_word_in, 3);

  // Mux input for SubWord
  assign sub_word_in = use_rot_word ? rot_word_out : rot_word_in;

  // SubWord - individually substitute bytes
  for (genvar i = 0; i < 4; i++) begin : gen_sbox
    aes_sbox #(
      .SBoxImpl ( SBoxImpl )
    ) aes_sbox_i (
      .op_i   ( CIPH_FWD               ),
      .data_i ( sub_word_in[8*i +: 8]  ),
      .data_o ( sub_word_out[8*i +: 8] )
    );
  end

  // Add Rcon
  assign rcon_add_in  = sub_word_out[7:0];
  assign rcon_add_out = rcon_add_in ^ rcon_q;
  assign rcon_added   = {sub_word_out[31:8], rcon_add_out};

  // Mux output coming from Rcon & SubWord
  assign irregular = use_rcon ? rcon_added : sub_word_out;

  ///////////////////////////
  // The more regular part //
  ///////////////////////////

  // To reduce muxing resources, we re-use existing
  // connections for unused words and default cases.
  always_comb begin : drive_regular
    unique case (key_len_i)

      /////////////
      // AES-128 //
      /////////////
      AES_128: begin
        // key_o[7:4] not used
        regular[7:4] = key_i[3:0];

        regular[0] = irregular ^ key_i[0];
        unique case (op_i)
          CIPH_FWD: begin
            for (int i=1; i<4; i++) begin
              regular[i] = regular[i-1] ^ key_i[i];
            end
          end

          CIPH_INV: begin
            for (int i=1; i<4; i++) begin
              regular[i] = key_i[i-1] ^ key_i[i];
            end
          end

          default: regular = {key_i[3:0], key_i[7:4]};
        endcase
      end

      /////////////
      // AES-192 //
      /////////////
      AES_192: begin
        // key_o[7:6] not used
        regular[7:6] = key_i[3:2];

        if (AES192Enable) begin
          unique case (op_i)
            CIPH_FWD: begin
              if (rnd_type[0]) begin
                // Shift down four upper most words
                regular[3:0] = key_i[5:2];
                // Generate Words 6 and 7
                regular[4]   = irregular  ^ key_i[0];
                regular[5]   = regular[4] ^ key_i[1];
              end else begin
                // Shift down two upper most words
                regular[1:0] = key_i[5:4];
                // Generate new upper four words
                for (int i=0; i<4; i++) begin
                  if ((i == 0 && rnd_type[2]) ||
                      (i == 2 && rnd_type[3])) begin
                    regular[i+2] = irregular    ^ key_i[i];
                  end else begin
                    regular[i+2] = regular[i+1] ^ key_i[i];
                  end
                end
              end // rnd_type[0]
            end

            CIPH_INV: begin
              if (rnd_type[0]) begin
                // Shift up four lowest words
                regular[5:2] = key_i[3:0];
                // Generate Word 44 and 45
                for (int i=0; i<2; i++) begin
                  regular[i] = key_i[3+i] ^ key_i[3+i+1];
                end
              end else begin
                // Shift up two lowest words
                regular[5:4] = key_i[1:0];
                // Generate new lower four words
                for (int i=0; i<4; i++) begin
                  if ((i == 2 && rnd_type[1]) ||
                      (i == 0 && rnd_type[2])) begin
                    regular[i] = irregular  ^ key_i[i+2];
                  end else begin
                    regular[i] = key_i[i+1] ^ key_i[i+2];
                  end
                end
              end // rnd_type[0]
            end

            default: regular = {key_i[3:0], key_i[7:4]};
          endcase

        end else begin
          regular = {key_i[3:0], key_i[7:4]};
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
              regular = {key_i[3:0], key_i[7:4]};
            end else begin
              // Shift down old upper half
              regular[3:0] = key_i[7:4];
              // Generate new upper half
              regular[4]   = irregular ^ key_i[0];
              for (int i=1; i<4; i++) begin
                regular[i+4] = regular[i+4-1] ^ key_i[i];
              end
            end // rnd == 0
          end

          CIPH_INV: begin
            if (rnd == 0) begin
              // Round 0: Nothing to be done
              // The Full Key registers are not updated
              regular = {key_i[3:0], key_i[7:4]};
            end else begin
              // Shift up old lower half
              regular[7:4] = key_i[3:0];
              // Generate new lower half
              regular[0]   = irregular ^ key_i[4];
              for (int i=0; i<3; i++) begin
                regular[i+1] = key_i[4+i] ^ key_i[4+i+1];
              end
            end // rnd == 0
          end

          default: regular = {key_i[3:0], key_i[7:4]};
        endcase
      end

      default: regular = {key_i[3:0], key_i[7:4]};
    endcase // key_len_i
  end

  // Drive output
  assign key_o = regular;

  // Selectors must be known/valid
  `ASSERT_KNOWN(AesCiphOpKnown, op_i)
  `ASSERT(AesKeyLenValid, key_len_i inside {
      AES_128,
      AES_192,
      AES_256
      })

endmodule
