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
  localparam int NumStimulus = 9*4,
  localparam int NumResponses = 2*4
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
    stimulus = '{
      // NONCE
      put_full_data(32'hDEADBEEF, ASCON_NONCE_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE0_1_OFFSET),
      put_full_data(32'h01234567, ASCON_NONCE_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_NONCE_SHARE1_0_OFFSET),
      put_full_data(32'hCAFECAFE, ASCON_NONCE_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_NONCE_SHARE1_2_OFFSET),
      put_full_data(32'h89ABCDEF, ASCON_NONCE_SHARE1_3_OFFSET),

      // KEY
      put_full_data(32'hDEADBEEF, ASCON_KEY_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE0_1_OFFSET),
      put_full_data(32'h01234567, ASCON_KEY_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_KEY_SHARE1_0_OFFSET),
      put_full_data(32'hCAFECAFE, ASCON_KEY_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_KEY_SHARE1_2_OFFSET),
      put_full_data(32'h89ABCDEF, ASCON_KEY_SHARE1_3_OFFSET),

      // DATA
      put_full_data(32'hDEADBEEF, ASCON_DATA_IN_SHARE0_0_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_1_OFFSET),
      put_full_data(32'h01234567, ASCON_DATA_IN_SHARE0_2_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE0_3_OFFSET),

      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_0_OFFSET),
      put_full_data(32'hCAFECAFE, ASCON_DATA_IN_SHARE1_1_OFFSET),
      put_full_data(32'h0, ASCON_DATA_IN_SHARE1_2_OFFSET),
      put_full_data(32'h89ABCDEF, ASCON_DATA_IN_SHARE1_3_OFFSET),

      // TAG
      put_full_data(32'hDEADBEEF, ASCON_TAG_IN_0_OFFSET),
      put_full_data(32'h0, ASCON_TAG_IN_1_OFFSET),
      put_full_data(32'h01234567, ASCON_TAG_IN_2_OFFSET),
      put_full_data(32'h0, ASCON_TAG_IN_3_OFFSET),

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
      expect_full_data(32'hDEADBEEF),
      expect_full_data(32'hCAFECAFE),
      expect_full_data(32'h01234567),
      expect_full_data(32'h89ABCDEF),

      // TAG
      expect_full_data(32'hDEADBEEF),
      expect_full_data(32'h0),
      expect_full_data(32'h01234567),
      expect_full_data(32'h0)
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

  assign done_o = (response_counter == NumResponses-1)
                  && (stimulus_counter == NumStimulus) ? 1'b1 : 1'b0;

endmodule
