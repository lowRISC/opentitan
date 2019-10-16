// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES KeyExpand

module aes_key_expand #(
  parameter bit AES192Enable = 1
) (
  input  logic              clk_i,
  input  logic              rst_ni,
  input  aes_pkg::mode_e    mode_i,
  input  logic              step_i,
  input  logic              clear_i,
  input  logic [3:0]        round_i,
  input  aes_pkg::key_len_e key_len_i,
  input  logic [31:0]       key_i [8],
  output logic [31:0]       key_o [8]
);

  import aes_pkg::*;

  logic  [7:0] rcon_d, rcon_q;
  logic        rcon_we;
  logic        use_rcon;

  logic  [3:0] rnd;
  logic  [3:0] rnd_type;

  logic [31:0] spec_in_128, spec_in_192;
  logic [31:0] rot_word_in, rot_word_out;
  logic        use_rot_word;
  logic [31:0] sub_word_in, sub_word_out;
  logic  [7:0] rcon_add_in, rcon_add_out;
  logic [31:0] rcon_added;

  logic [31:0] irregular;
  logic [31:0] regular[8];

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

  // Depending on key length and round, RotWord is not used
  assign use_rot_word = (key_len_i == AES_256 && rnd[0] == 1'b0) ? 1'b0 : 1'b1;

  // Depending on mode, key length and round, Rcon is not used and thus must not be updated
  always_comb begin : rcon_usage
    use_rcon = 1'b1;

    if (AES192Enable) begin
      if (key_len_i == AES_192 &&
          ((mode_i == AES_ENC &&  rnd_type[1]) ||
           (mode_i == AES_DEC && (rnd_type[0] || rnd_type[3])))) begin
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
      rcon_d =  (mode_i == AES_ENC)                            ? 8'h01 :
               ((mode_i == AES_DEC) && (key_len_i == AES_128)) ? 8'h36 :
               ((mode_i == AES_DEC) && (key_len_i == AES_192)) ? 8'h80 :
               ((mode_i == AES_DEC) && (key_len_i == AES_256)) ? 8'h40 : 8'hXX;
    end else begin
      rcon_d =  (mode_i == AES_ENC) ? aes_mul2(rcon_q) :
                (mode_i == AES_DEC) ? aes_div2(rcon_q) : 8'hXX;
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
  assign spec_in_192 = AES192Enable ?  key_i[5] ^ key_i[1] ^ key_i[0] : '0;

  // Select input
  always_comb begin : rot_word_in_mux
    unique case (key_len_i)

      /////////////
      // AES-128 //
      /////////////
      AES_128: begin
        unique case (mode_i)
          AES_ENC: rot_word_in = key_i[3];
          AES_DEC: rot_word_in = spec_in_128;
          default: rot_word_in = 'X;
        endcase
      end

      /////////////
      // AES-192 //
      /////////////
      AES_192: begin
        if (AES192Enable) begin
          unique case (mode_i)
            AES_ENC: begin
              rot_word_in = rnd_type[0] ? key_i[5]    :
                            rnd_type[2] ? key_i[5]    :
                            rnd_type[3] ? spec_in_192 : 'X;
            end
            AES_DEC: begin
              rot_word_in = rnd_type[1] ? key_i[3] :
                            rnd_type[2] ? key_i[1] : 'X;
            end
            default: rot_word_in = 'X;
          endcase
        end else begin
          rot_word_in = 'X;
        end
      end

      /////////////
      // AES-256 //
      /////////////
      AES_256: begin
        unique case (mode_i)
          AES_ENC: rot_word_in = key_i[7];
          AES_DEC: rot_word_in = key_i[3];
          default: rot_word_in = 'X;
        endcase
      end

      default: rot_word_in = 'X;
    endcase
  end

  // RotWord: cyclic byte shift
  assign rot_word_out = {rot_word_in[7:0], rot_word_in[31:8]};

  // Mux input for SubWord
  assign sub_word_in = use_rot_word ? rot_word_out : rot_word_in;

  // SubWord - individually substitute bytes
  for (genvar i = 0; i < 4; i++) begin : gen_sbox
    aes_sbox_lut aes_sbox_i (
      .mode_i ( AES_ENC   ),
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
  always_comb begin : drive_regular
    unique case (key_len_i)

      /////////////
      // AES-128 //
      /////////////
      AES_128: begin
        // key_o[4:7] not used
        regular[4:7] = '{default: 'X};

        regular[0] = irregular ^ key_i[0];
        unique case (mode_i)
          AES_ENC: begin
            for (int i=1; i<4; i++) begin
              regular[i] = regular[i-1] ^ key_i[i];
            end
          end

          AES_DEC: begin
            for (int i=1; i<4; i++) begin
              regular[i] = key_i[i-1] ^ key_i[i];
            end
          end

          default: regular = '{default: 'X};
        endcase
      end

      /////////////
      // AES-192 //
      /////////////
      AES_192: begin
        // key_o[6:7] not used
        regular[6:7] = '{default: 'X};

        if (AES192Enable) begin
          unique case (mode_i)
            AES_ENC: begin
              if (rnd_type[0]) begin
                // Shift down four upper most words
                regular[0:3] = key_i[2:5];
                // Generate Words 6 and 7
                regular[4]   = irregular  ^ key_i[0];
                regular[5]   = regular[4] ^ key_i[1];
              end else begin
                // Shift down two upper most words
                regular[0:1] = key_i[4:5];
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

            AES_DEC: begin
              if (rnd_type[0]) begin
                // Shift up four lowest words
                regular[2:5] = key_i[0:3];
                // Generate Word 44 and 45
                for (int i=0; i<2; i++) begin
                  regular[i] = key_i[3+i] ^ key_i[3+i+1];
                end
              end else begin
                // Shift up two lowest words
                regular[4:5] = key_i[0:1];
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

            default: regular = '{default: 'X};
          endcase

        end else begin
          regular = '{default: 'X};
        end // AES192Enable
      end

      /////////////
      // AES-256 //
      /////////////
      AES_256: begin
        unique case (mode_i)
          AES_ENC: begin
            if (rnd == 0) begin
              // Round 0: Nothing to be done
              regular = key_i;
            end else begin
              // Shift down old upper half
              regular[0:3] = key_i[4:7];
              // Generate new upper half
              regular[4]   = irregular ^ key_i[0];
              for (int i=1; i<4; i++) begin
                regular[i+4] = regular[i+4-1] ^ key_i[i];
              end
            end // rnd == 0
          end

          AES_DEC: begin
            if (rnd == 0) begin
              // Round 0: Nothing to be done
              regular = key_i;
            end else begin
              // Shift up old lower half
              regular[4:7] = key_i[0:3];
              // Generate new lower half
              regular[0]   = irregular ^ key_i[4];
              for (int i=0; i<3; i++) begin
                regular[i+1] = key_i[4+i] ^ key_i[4+i+1];
              end
            end // rnd == 0
          end

          default: regular = '{default: 'X};
        endcase
      end

      default: regular = '{default: 'X};
    endcase // key_len_i
  end

  // Drive output
  assign key_o = regular;

endmodule
