// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon simulation wrapper

module ascon_tl_ul_stim
  import ascon_pkg::*;
  import tlul_pkg::*;
  import ascon_reg_pkg::*;
  import ascon_tl_ul_stim_pkg::*;
#(
  localparam int NumStimulus = 13*4 + 4*2 + 1,
  localparam int NumResponses = 3*4
)
(
  input  clk_i,
  input  rst_ni,

  output tl_d2h_t expected_tlul_resonse_o,
  output tl_h2d_t tlul_stimulus_o,

  input pop_next_stimulus_i,
  input pop_next_response_i,

  output done_o
);

  tl_h2d_t stimulus[NumStimulus];
  tl_h2d_t stimulus_selected;
  tl_h2d_t stimulus_data_intg;
  tl_d2h_t response[NumResponses];

  initial begin
    // The idea of this test case is to have human readable (DEADBEEF, CAFEF00D, etc) test vectors,
    // that are easy to trace troughout the design to catch logical errors (endianness,
    // clock delays, etc.) during development.
    stimulus = '{
      // NONCE
      put_full_data(32'h0, ASCON_NONCE_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE0_1_OFFSET),
      put_full_data(32'hEFBEADDE, ASCON_NONCE_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_NONCE_SHARE1_0_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE1_2_OFFSET),
      put_full_data(32'h0DF0FECA, ASCON_NONCE_SHARE1_3_OFFSET),

      // KEY
      put_full_data(32'hEFBEADDE, ASCON_KEY_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE0_1_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_KEY_SHARE1_0_OFFSET),
      put_full_data(32'h0DF0FECA, ASCON_KEY_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE1_2_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE1_3_OFFSET),

      //Varaint+ Operation:
      // 5'b01_001 :  Ascon-128 Enc
      put_full_data(32'h00000009, ASCON_CTRL_SHADOWED_OFFSET),
      put_full_data(32'h00000009, ASCON_CTRL_SHADOWED_OFFSET),

      // BLock Info
      // 3 bits reserved, 5 bits valid_bytes, 12 bits last, 12 bist start (ignored)
      // Full 64 bit block AD, last
      put_full_data(32'h08969000, ASCON_BLOCK_CTRL_SHADOWED_OFFSET),
      put_full_data(32'h08969000, ASCON_BLOCK_CTRL_SHADOWED_OFFSET),

      // AD
      put_full_data(32'h78563412, ASCON_DATA_IN_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_0_OFFSET),
      put_full_data(32'hF0DEBC9A, ASCON_DATA_IN_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_3_OFFSET),

      // Trigger start
      put_full_data(32'h00000001, ASCON_TRIGGER_OFFSET),

      // BLock Info
      // 3 bits reserved, 5 bits valid_bytes, 12 bits last, 12 bist start (ignored)
      // Full 64 bit block msg, last
      put_full_data(32'h08999000, ASCON_BLOCK_CTRL_SHADOWED_OFFSET),
      put_full_data(32'h08999000, ASCON_BLOCK_CTRL_SHADOWED_OFFSET),

      // MSG
      put_full_data(32'hEFBEADDE, ASCON_DATA_IN_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_0_OFFSET),
      put_full_data(32'h0DF0FECA, ASCON_DATA_IN_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_3_OFFSET),

      // TAG
      //put_full_data(32'hDEADBEEF, ASCON_TAG_IN_0_OFFSET),
      //put_full_data(32'h0, ASCON_TAG_IN_1_OFFSET),
      //put_full_data(32'h01234567, ASCON_TAG_IN_2_OFFSET),
      //put_full_data(32'h0, ASCON_TAG_IN_3_OFFSET),

      // GET MSG
      get_full_data(ASCON_MSG_OUT_0_OFFSET),
      get_full_data(ASCON_MSG_OUT_1_OFFSET),
      get_full_data(ASCON_MSG_OUT_2_OFFSET),
      get_full_data(ASCON_MSG_OUT_3_OFFSET),

      // BLock Info
      // 3 bits reserved, 5 bits valid_bytes, 12 bits last, 12 bist start (ignored)
      // Full 64 bit block msg, last
      put_full_data(32'h02699000, ASCON_BLOCK_CTRL_SHADOWED_OFFSET),
      put_full_data(32'h02699000, ASCON_BLOCK_CTRL_SHADOWED_OFFSET),
            // DATA
      put_full_data(32'hF0F0F0F0, ASCON_DATA_IN_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_0_OFFSET),
      put_full_data(32'hE0E0E0E0, ASCON_DATA_IN_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_3_OFFSET),

      // GET MSG
      get_full_data(ASCON_MSG_OUT_0_OFFSET),
      get_full_data(ASCON_MSG_OUT_1_OFFSET),
      get_full_data(ASCON_MSG_OUT_2_OFFSET),
      get_full_data(ASCON_MSG_OUT_3_OFFSET),

      // GET TAG
      get_full_data(ASCON_TAG_OUT_0_OFFSET),
      get_full_data(ASCON_TAG_OUT_1_OFFSET),
      get_full_data(ASCON_TAG_OUT_2_OFFSET),
      get_full_data(ASCON_TAG_OUT_3_OFFSET)
    };

    response = '{
      // MESG
      expect_full_data(32'h057F25B4),
      expect_full_data(32'hA9481060),
      expect_full_data(32'h00000000),
      expect_full_data(32'h00000000),

      // MESG
      expect_full_data(32'h00005A47),
      expect_full_data(32'h00000000),
      expect_full_data(32'h00000000),
      expect_full_data(32'h00000000),

      // TAG
      expect_full_data(32'h71151ABF),
      expect_full_data(32'h95BD8BDB),
      expect_full_data(32'h8387BE47),
      expect_full_data(32'h79927DD5)
    };
  end

  int stimulus_counter;
  int response_counter;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_stimulus
    if (!rst_ni) begin
      stimulus_counter <= 0;
    end else if (pop_next_stimulus_i) begin
      stimulus_counter <= stimulus_counter+1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_response
    if (!rst_ni) begin
      response_counter <= 0;
    end else if (pop_next_response_i) begin
      response_counter <= response_counter+1;
    end
  end

  logic [38:0] data_39_32_enc;
  tlul_data_integ_enc #(
  ) u_tlul_data_integ_enc (
    .data_i(stimulus_selected.a_data),
    .data_intg_o(data_39_32_enc)
  );

  always_comb begin
    stimulus_data_intg = stimulus_selected;
    stimulus_data_intg.a_user.data_intg = data_39_32_enc[38:32];
  end

  tlul_cmd_intg_gen #(
  ) u_tlul_cmd_intg_gen (
      .tl_i (stimulus_data_intg),
      .tl_o (tlul_stimulus_o)
  );

  assign expected_tlul_resonse_o = response[response_counter];

  always_comb begin
    if (stimulus_counter < NumStimulus) begin
      stimulus_selected = stimulus[stimulus_counter];
    end else begin
      stimulus_selected = TL_H2D_DEFAULT;
    end
  end

  assign done_o = (response_counter >= NumResponses-1)
                  && (stimulus_counter >= NumStimulus) ? 1'b1 : 1'b0;

endmodule
