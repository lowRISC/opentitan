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

  logic [7:0] rcon_d, rcon_q;
  logic       rcon_we;
  logic       rcon_use;
  logic [3:0] rnd;

  // generate rcon
  always_comb begin : rcon_update
    rcon_d = rcon_q;

    if (clear_i) begin
      rcon_d =  (mode_i == AES_ENC)                            ? 8'h01 :
               ((mode_i == AES_DEC) && (key_len_i == AES_128)) ? 8'h36 :
               ((mode_i == AES_DEC) && (key_len_i == AES_192)) ? 8'h80 :
               ((mode_i == AES_DEC) && (key_len_i == AES_256)) ? 8'h40 : 8'hXX;
    end else begin
      if (mode_i == AES_ENC) begin
        rcon_d = {rcon_q[6],
                  rcon_q[5],
                  rcon_q[4],
                  rcon_q[3] ^ rcon_q[7],
                  rcon_q[2] ^ rcon_q[7],
                  rcon_q[1],
                  rcon_q[0] ^ rcon_q[7],
                  rcon_q[7]};

      end else if (mode_i == AES_DEC) begin
        rcon_d = {rcon_q[0],
                  rcon_q[7],
                  rcon_q[6],
                  rcon_q[5],
                  rcon_q[4] ^ rcon_q[0],
                  rcon_q[3] ^ rcon_q[0],
                  rcon_q[2],
                  rcon_q[1] ^ rcon_q[0]};

      end else begin
        rcon_d = 8'hXX;
      end
    end
  end

  // depending on mode, key length and round, rcon is not used and thus must not be updated
  assign rnd = round_i;
  always_comb begin : rcon_usage
    rcon_use = 1'b1;

    if (AES192Enable) begin
      if (key_len_i == AES_192 &&
          ((mode_i == AES_ENC && (rnd == 1 || rnd == 4 || rnd == 7 || rnd == 10)) ||
           (mode_i == AES_DEC && (rnd == 0 || rnd == 3 || rnd == 6 || rnd == 9)))) begin
        rcon_use = 1'b0;
      end
    end

    if (key_len_i == AES_256 &&
        ((mode_i == AES_ENC && round_i[0] == 1'b0) ||
         (mode_i == AES_DEC && round_i[0] == 1'b1))) begin
      rcon_use = 1'b0;
    end
  end

  assign rcon_we = clear_i | (step_i & rcon_use);

  // dummy only
  assign key_o = key_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_rcon
    if (!rst_ni) begin
      rcon_q <= '0;
    end else if (rcon_we) begin
      rcon_q <= rcon_d;
    end
  end

endmodule
