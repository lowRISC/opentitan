// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon duplex testbench

module prim_ascon_duplex_tb (
  input  logic clk_i,
  input  logic rst_ni,

  output logic test_done_o,
  output logic test_passed_o
);

  import ascon_model_dpi_pkg::*;
  import prim_ascon_duplex_tb_pkg::*;
  import prim_ascon_pkg::*;
  import prim_mubi_pkg::*;

  parameter int NUMB_RUNS = 100;

  // TODO: Problem: the c dpi model of Ascon128a and Ascon128a cannot be compiled
  //       at the same time, due to the structure in the vendor code.
  // TODO: Use streaming operator instead of for loops?

  parameter duplex_op_e OPERATION = ASCON_ENC;
  parameter duplex_variant_e VARIANT = ASCON_128;
  localparam int unsigned BLOCKSIZE = VARIANT == ASCON_128 ? 8 : 16;

  parameter int STIMULUS_MSG_LEN = 10;
  localparam int EXPECTED_CT_LEN = STIMULUS_MSG_LEN +16;
  byte unsigned stimulus_msg[STIMULUS_MSG_LEN];
  assign stimulus_msg = '{'hDE, 'hAD, 'hBE, 'hEF, 'hCA, 'hFE, 'hF0, 'h0D,
                          'hF0, 'hF0};//, 'hF0, 'hF0, 'hE0, 'hE0,'hE0, 'hE0};

  parameter int STIMULUS_CT_LEN = 10;
  localparam int EXPECTED_MSG_LEN = STIMULUS_CT_LEN;
  byte unsigned stimulus_ct[STIMULUS_CT_LEN];
  assign stimulus_ct = '{'hDE, 'hAD, 'hBE, 'hEF, 'hCA, 'hFE, 'hF0, 'h0D,
                         'hF0, 'hF0};//, 'hF0, 'hF0, 'hE0, 'hE0,'hE0, 'hE0};

  parameter int STIMULUS_AD_LEN  = 8;
  byte unsigned  stimulus_ad[STIMULUS_AD_LEN];
  assign stimulus_ad  = '{'h12, 'h34, 'h56, 'h78, 'h9A, 'hBC, 'hDE, 'hF0};//,
                         // 'hF0, 'hF0, 'hF0, 'hF0, 'hE0, 'hE0, 'hE0, 'hE0};

  logic [127:0] key;
  logic [127:0] nonce;

  assign   key = 128'hDEAD_BEEF_CAFE_F00D_0000_0000_0000_0000;
  assign nonce = 128'h0000_0000_0000_0000_DEAD_BEEF_CAFE_F00D;

  byte unsigned   c_key[16];
  byte unsigned c_nonce[16];

  // convert logic <=> byte array for c_dpi call
  for (genvar i = 0; i < 16; i++) begin : g_key_array
    assign c_key[i]   =   key[127 - 8*i : 120 - 8*i];
    assign c_nonce[i] = nonce[127 - 8*i : 120 - 8*i];
  end

  // in the c modle the tag is part of the ciphertext
  byte unsigned  expected_ct[EXPECTED_CT_LEN];
  byte unsigned    actual_ct[EXPECTED_CT_LEN];

  // in the c modle the tag is part of the ciphertext
  byte unsigned  expected_msg[EXPECTED_MSG_LEN];
  byte unsigned    actual_msg[EXPECTED_MSG_LEN];
  byte unsigned   actual_tag[16];
  byte unsigned expected_tag[16];
  assign expected_tag = '{'hDE, 'hAD, 'hBE, 'hEF, 'hCA, 'hFE, 'hF0, 'h0D,
                         'hF0, 'hF0, 'hF0, 'hF0, 'hE0, 'hE0,'hE0, 'hE0};

  byte unsigned ct_tag_input[STIMULUS_CT_LEN+16];

  for (genvar i = 0; i < STIMULUS_CT_LEN; i++ ) begin : g_ct_tag_input1
    assign ct_tag_input[i] = stimulus_ct[i];
  end

  for (genvar i = 0; i < 16; i++) begin : g_ct_tag_input2
    assign ct_tag_input[STIMULUS_CT_LEN + i] = expected_tag[i];
  end

  always_comb begin : C_DPI
    if (OPERATION == ASCON_ENC) begin
      c_dpi_aead_encrypt(expected_ct,
                        stimulus_msg, STIMULUS_MSG_LEN,
                        stimulus_ad, STIMULUS_AD_LEN,
                        c_nonce, c_key);

    end else begin
      //TODO check return value for tag missmatch
      c_dpi_aead_decrypt(ct_tag_input, (STIMULUS_CT_LEN+16),
                        expected_msg,
                        stimulus_ad, STIMULUS_AD_LEN,
                        c_nonce, c_key);
    end
  end

  int unsigned ad_count_d, ad_count_q;
  int unsigned msg_count_d, msg_count_q;
  int unsigned ct_count_d, ct_count_q;

  fsm_tb_state_e tb_state, nxt_tb_state;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tb_state <= Idle;
      msg_count_q <= 0;
      ad_count_q <= 0;
      ct_count_q <= 0;
    end else begin
      tb_state <= nxt_tb_state;
      msg_count_q <= msg_count_d;
      ad_count_q <= ad_count_d;
      ct_count_q <= ct_count_d;
    end
  end

  for (genvar i = 0; i < BLOCKSIZE; i++) begin : g_dut_input
  // TODO double check for out of bounds: Looks like this is working, but we should add
  // more information why.
    assign  dut_input_data_ad[127 - 8*i : 120 - 8*i] =  stimulus_ad[(ad_count_q * BLOCKSIZE) + i];
    assign dut_input_data_msg[127 - 8*i : 120 - 8*i] = stimulus_msg[(msg_count_q * BLOCKSIZE) + i];
    assign  dut_input_data_ct[127 - 8*i : 120 - 8*i] =  stimulus_ct[(ct_count_q * BLOCKSIZE) + i];
  end

  for (genvar i = 0; i < BLOCKSIZE; i++) begin : g_dut_response_data
  // TODO double check for out of bounds: Looks like this is working, but we should add
  // more information why.
    always_ff @(posedge clk_i) begin
      if (dut_response_data_valid) begin
        actual_ct[(msg_count_q * BLOCKSIZE) + i] <= dut_response_data[127 - 8*i : 120 - 8*i];
        actual_msg[(ct_count_q * BLOCKSIZE) + i] <= dut_response_data[127 - 8*i : 120 - 8*i];
      end
    end
  end

  for (genvar i = 0; i < 16; i++) begin : g_dut_response_tag
    always_ff @(posedge clk_i) begin
      if (dut_response_tag_valid) begin
        actual_ct[STIMULUS_MSG_LEN+i] <= dut_response_tag[127 - 8*i : 120 - 8*i];
        actual_tag[i] <= dut_response_tag[127 - 8*i : 120 - 8*i];
      end
    end
  end

  always_comb begin
    nxt_tb_state = tb_state;
    start = 1'b0;
    dut_input_valid = 1'b0;
    dut_last_block_msg = MuBi4False;
    dut_last_block_ad = MuBi4False;
    msg_count_d = msg_count_q;
    ct_count_d = ct_count_q;
    ad_count_d = ad_count_q;
    fsm_done = 1'b0;
    dut_input_data = 'h0;

    unique case (tb_state)
      Idle: begin
        start = 1'b1;
        if (STIMULUS_AD_LEN > 0) begin
          nxt_tb_state = SendAD;
        end else begin
          nxt_tb_state = CheckMSGLen;
        end
      end
      SendAD: begin
        dut_input_valid = 1'b1;
        dut_input_data = dut_input_data_ad;
        if ((ad_count_q + 1) * BLOCKSIZE < STIMULUS_AD_LEN) begin
         dut_data_valid_bytes = 5'(BLOCKSIZE);
         dut_last_block_ad = MuBi4False;
        end else begin
         dut_data_valid_bytes = 5'(STIMULUS_AD_LEN - ((ad_count_q) * 8));
         dut_last_block_ad = MuBi4True;
        end
        if (dut_read_data) begin
          nxt_tb_state = WaitADRead;
        end
      end
      WaitADRead: begin
        if ((ad_count_q + 1) * BLOCKSIZE < STIMULUS_AD_LEN) begin
          ad_count_d = ad_count_q +1;
          nxt_tb_state = SendAD;
        end else begin
          if (OPERATION == ASCON_ENC) begin
            nxt_tb_state = CheckMSGLen;
          end else begin
            nxt_tb_state = CheckCTLen;
          end
        end
      end
      CheckMSGLen: begin
        if (STIMULUS_MSG_LEN > 0) begin
          nxt_tb_state = SendMSG;
        end else begin
          nxt_tb_state = ReceiveTag;
        end
      end
      SendMSG: begin
        dut_input_valid = 1'b1;
        dut_input_data = dut_input_data_msg;
        if ((msg_count_q + 1) * BLOCKSIZE < STIMULUS_MSG_LEN) begin
          dut_data_valid_bytes = 5'(BLOCKSIZE);
          dut_last_block_msg = MuBi4False;
        end else begin
          dut_data_valid_bytes = 5'(STIMULUS_MSG_LEN - (msg_count_q * BLOCKSIZE));
          dut_last_block_msg = MuBi4True;
        end
        if (dut_read_data) begin
          nxt_tb_state = WaitMSGRead;
        end
      end
      WaitMSGRead: begin
        if ((msg_count_q + 1) * 8 < STIMULUS_MSG_LEN) begin
          msg_count_d = msg_count_q + 1;
          nxt_tb_state = SendMSG;
        end else begin
          nxt_tb_state = ReceiveTag;
        end
      end
      ReceiveTag: begin
        if (dut_response_tag_valid) begin
          nxt_tb_state = WaitForEver;
        end
      end

      CheckCTLen: begin
        if (EXPECTED_MSG_LEN > 0) begin
          nxt_tb_state = SendCT;
        end else begin
          nxt_tb_state = VerifyTag;
        end
      end
      SendCT: begin
        dut_input_valid = 1'b1;
        dut_input_data = dut_input_data_ct;
        if ((ct_count_q + 1) * BLOCKSIZE < STIMULUS_CT_LEN) begin
          dut_data_valid_bytes = 5'(BLOCKSIZE);
          dut_last_block_msg = MuBi4False;
        end else begin
          dut_data_valid_bytes = 5'(EXPECTED_MSG_LEN - (msg_count_q * BLOCKSIZE));
          dut_last_block_msg = MuBi4True;
        end
        if (dut_read_data) begin
          nxt_tb_state = WaitCTRead;
        end
      end
      WaitMSGRead: begin
        if ((ct_count_q + 1) * 8 < EXPECTED_MSG_LEN) begin
          ct_count_d = ct_count_q + 1;
          nxt_tb_state = SendCT;
        end else begin
          nxt_tb_state = VerifyTag;
        end
      end
      ReceiveTag: begin
        if (dut_response_tag_valid) begin
          nxt_tb_state = WaitForEver;
        end
      end
      WaitForEver: begin
        fsm_done = 1'b1;
      end
      default: nxt_tb_state = tb_state;
    endcase
  end


  //generate the sequential input/output for the DUT:

  logic [127:0] dut_input_data;
  logic [127:0] dut_input_data_ad;
  logic [127:0] dut_input_data_msg;
  logic [127:0] dut_input_data_ct;
  logic         dut_input_valid;

  logic  [4:0] dut_data_valid_bytes;
  logic        dut_read_data;

  logic [127:0] dut_response_data;
  logic         dut_response_data_valid;

  logic [127:0] dut_response_tag;
  logic         dut_response_tag_valid;

  logic dut_no_msg;
  logic dut_no_ad;

  assign dut_no_msg =
         ((OPERATION == ASCON_ENC && STIMULUS_MSG_LEN == 0)
        ||(OPERATION == ASCON_DEC && EXPECTED_MSG_LEN == 0))
         ? 1'b1 : 1'b0;
  assign dut_no_ad  = STIMULUS_AD_LEN  == 0 ? 1'b1 : 1'b0;

  mubi4_t dut_last_block_ad;
  mubi4_t dut_last_block_msg;

  logic idle;
  logic start;
  logic fsm_done;


  // Instantiate Ascon Duplex
  prim_ascon_duplex ascon_duplex (

  .clk_i(clk_i),
  .rst_ni(rst_ni),

  .ascon_variant(VARIANT),
  .ascon_operation(OPERATION),

  .start_i(start),
  .idle_o(idle),

  // It is assumed that no_ad, no_msg, key, and nonce are always
  // valid and constant, when the cipher is triggered by the start command
  .no_ad(dut_no_ad),
  .no_msg(dut_no_msg),

  .key_i(key),
  .nonce_i(nonce),

  // Cipher Input Port
  .data_in_i(dut_input_data),
  .data_in_valid_bytes_i(dut_data_valid_bytes),
  .last_block_ad_i(dut_last_block_ad),
  .last_block_msg_i(dut_last_block_msg),
  .data_in_valid_i(dut_input_valid),
  .data_in_read_o(dut_read_data),

  // Cipher Output Port
  .data_out_o(dut_response_data),
  // TODO: Test backpreasure
  .data_out_read_i(1'b1),
  .data_out_we_o(dut_response_data_valid),

  .tag_out_o(dut_response_tag),
  .tag_out_we_o(dut_response_tag_valid),

  .err_o()
  );

  // Generate the runtime counter
  int count_d, count_q;
  assign count_d = count_q + 1;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_count
    if (!rst_ni) begin
      count_q <= 0;
    end else begin
      count_q <= count_d;
    end
  end

  initial begin
    test_done_o   = 1'b0;
    test_passed_o = 1'b1;
  end

  // Check responses, signal end of simulation
  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl
    if (rst_ni && fsm_done) begin
      if (OPERATION == ASCON_ENC) begin
        if (actual_ct != expected_ct) begin
          $display("\nERROR: Mismatch between DPI-based Ascon and Implementation found.");
          test_passed_o <= 1'b0;
          test_done_o   <= 1'b1;
        end
      end else begin
        if ((actual_msg != expected_msg) || (actual_tag != expected_tag)) begin
          $display("\nERROR: Mismatch between DPI-based Ascon and Implementation found.");
          test_passed_o <= 1'b0;
          test_done_o   <= 1'b1;
        end
      end
    end

    if (count_q == NUMB_RUNS) begin
      $display("\nSUCCESS: Outputs matches.");
      test_done_o <= 1'b1;
    end
  end

endmodule
