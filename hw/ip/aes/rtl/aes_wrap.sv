// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES SBox testbench

module aes_wrap
  import aes_pkg::*;
#(
  parameter bit         AES192Enable = 0,           // Can be 0 (disable), or 1 (enable).
  parameter bit         Masking      = 0,           // Can be 0 (no masking), or
                                                    // 1 (first-order masking) of the cipher
                                                    // core. Masking requires the use of a
                                                    // masked S-Box, see SBoxImpl parameter.
                                                    // Note: currently, constant masks are
                                                    // used, this is of course not secure.
  parameter sbox_impl_e SBoxImpl     = SBoxImplLut  // See aes_pkg.sv
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic [127:0] aes_input,
  input  logic [127:0] aes_key,
  output logic [127:0] aes_output,

  output logic test_done_o,
  output logic test_passed_o
);

  import aes_pkg::*;
  import aes_reg_pkg::*;
  import tlul_pkg::*;

  logic unused_idle;
  logic edn_req;
  tl_h2d_t h2d, h2d_intg;  // req
  tl_d2h_t d2h;  // rsp
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] unused_alert_tx;
  assign alert_rx[0].ping_p = 1'b0;
  assign alert_rx[0].ping_n = 1'b1;
  assign alert_rx[0].ack_p  = 1'b0;
  assign alert_rx[0].ack_n  = 1'b1;
  assign alert_rx[1].ping_p = 1'b0;
  assign alert_rx[1].ping_n = 1'b1;
  assign alert_rx[1].ack_p  = 1'b0;
  assign alert_rx[1].ack_n  = 1'b1;

  // tlul_pkg::tl_h2d_t h2d_int; // req (internal)
  // tlul_pkg::tl_d2h_t d2h_int; // rsp (internal)

  // dv_utils_pkg::if_mode_e if_mode; // interface mode - Host or Device

  // prim_alert_pkg::alert_rx_t [aes_pkg::NumAlerts-1:0] alert_rx;
  // assign alert_rx[0] = 4'b0101;


  aes #(
    .AES192Enable(AES192Enable),
    .Masking(Masking),
    .SBoxImpl(SBoxImpl)
  ) aes (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .idle_o          (unused_idle),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .clk_edn_i       (clk_i),
    .rst_edn_ni      (rst_ni),
    .edn_o           (edn_req),
    .edn_i           ({edn_req, 1'b1, 32'h12345678}),
    .tl_i            (h2d_intg),
    .tl_o            (d2h),
    .alert_rx_i      (alert_rx),
    .alert_tx_o      (unused_alert_tx)
  );

  logic [31:0] count;
  // logic [31:0] reg_offset;
  logic [ 7:0] fsm;

  // logic [127:0] aes_input;
  // logic [127:0] aes_key;
  // logic [127:0] aes_output;

  tlul_cmd_intg_gen tlul_cmd_intg_gen (
    .tl_i(h2d),
    .tl_o(h2d_intg)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : tb_ctrl

    if (!rst_ni) begin
      count <= 32'b0;
      // aes_key <= 127'h2b7e1516_28aed2a6_abf71588_09cf4f3c;
      //00000000_00000000_00000000_00000000;//
      // aes_input <= 127'h6bc1bee2_2e409f96_e93d7e11_7393172a;
      //00000000_00000000_00000000_00000001;//
      // aes_input <= 127'h0000_0000_0000_0000;

      test_done_o <= 1'b0;
      test_passed_o <= 1'b0;
      // reg_offset <= 32'b0;
      fsm <= 8'b0;

      h2d.a_valid <= 1'b0;
      h2d.a_opcode <= PutFullData;  //3'b000;//32'b0;//
      h2d.a_param <= 3'b0;  //32'b0;//
      h2d.a_address <= 32'hFFFFFFFF;
      // manual_operation=manual, key_len=aes_128, mode=aes_ecb, operation=encrypt
      h2d.a_data     <= 32'hFFFFFFFF;
      h2d.a_source <= 8'hDE;  //32'b0;//
      h2d.a_size <= 2'b10;  //32'b0;//
      h2d.a_mask <= 4'b1111;
      //32'b0;//
      h2d.a_user.rsvd       <= '0;
      h2d.a_user.instr_type <= prim_mubi_pkg::MuBi4False;
      h2d.a_user.cmd_intg   <= '0;  // will be driven by tlul_cmd_intg_gen
      h2d.a_user.data_intg  <= '0;
      h2d.d_ready           <= 1'b1;
    end else begin

      count <= count + 32'h1;

      // below works
      if (fsm == 8'b0) begin
        if (count > 32'h20) begin
          fsm         <= {1'b1, AES_CTRL_SHADOWED_OFFSET};
          count       <= 32'b0;
          h2d.d_ready <= 1'b1;
          h2d.a_valid <= 1'b1;
        end
      end

      if (fsm == {1'b1, AES_CTRL_SHADOWED_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_CTRL_SHADOWED_OFFSET};
          // force_zero_masks=1, manual_operation=manual,
          // key_len=aes_128, mode=aes_ecb, operation=encrypt
          h2d.a_data <= {
            20'b00000000000000000000000, 1'b1, 1'b1, 3'b001, 6'b00_0001, 1'b0
          };
          h2d.a_mask <= 4'b1111;
        end
        if (count == 3) begin  // ctrl needs a few more cycles to setup than data
          fsm   <= {1'b1, AES_KEY_SHARE0_0_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_0_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_0_OFFSET};
          h2d.a_data    <= aes_key[31:0];  //32'b0;//$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_1_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_1_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_1_OFFSET};
          h2d.a_data    <= aes_key[63:32];  //32'b0;//$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_2_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_2_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_2_OFFSET};
          h2d.a_data    <= aes_key[95:64];  //32'b0;//$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_3_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_3_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_3_OFFSET};
          h2d.a_data    <= aes_key[127:96];  //32'b0;//$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_4_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_4_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_4_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_5_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_5_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_5_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_6_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_6_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_6_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE0_7_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE0_7_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE0_7_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_0_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_0_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_0_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_1_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_1_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_1_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_2_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_2_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_2_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_3_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_3_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_3_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_4_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_4_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_4_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_5_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_5_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_5_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_6_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_6_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_6_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_KEY_SHARE1_7_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_KEY_SHARE1_7_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_KEY_SHARE1_7_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_IV_0_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_IV_0_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_IV_0_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_IV_1_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_IV_1_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_IV_1_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_IV_2_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_IV_2_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_IV_2_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_IV_3_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_IV_3_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_IV_3_OFFSET};
          h2d.a_data    <= 32'b0;  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_DATA_IN_0_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_IN_0_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_IN_0_OFFSET};
          h2d.a_data    <= aes_input[31:0];  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_DATA_IN_1_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_IN_1_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_IN_1_OFFSET};
          h2d.a_data    <= aes_input[63:32];  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_DATA_IN_2_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_IN_2_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_IN_2_OFFSET};
          h2d.a_data    <= aes_input[95:64];  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_DATA_IN_3_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_IN_3_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_IN_3_OFFSET};
          h2d.a_data    <= aes_input[127:96];  //$random;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_TRIGGER_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_TRIGGER_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_TRIGGER_OFFSET};
          h2d.a_data    <= 32'h1;
          h2d.a_mask    <= 4'b1111;
        end
        if (count == 1) begin
          fsm   <= {1'b1, AES_STATUS_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_STATUS_OFFSET}) begin
        if (count % 32'h8 == 0) begin
          // h2d.a_valid    <= 1'b1;
          h2d.a_opcode  <= PutPartialData;  //3'b001;//32'b0;//
          h2d.a_address <= {25'b0, AES_STATUS_OFFSET};
        end

        if (|(d2h.d_data & 32'h8)) begin  // STATUS = OUTPUT_VALID
          fsm   <= {1'b1, AES_DATA_OUT_0_OFFSET};
          count <= 32'b0;
        end

        // $display("AES_STATUS_OFFSET %0h.", d2h.d_data);
      end
      // above works

      if (fsm == {1'b1, AES_DATA_OUT_0_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_OUT_0_OFFSET};
        end
        if (count == 3) begin  // these reads also take more cycles to have data ready
          // $display("AES_DATA_OUT_0_OFFSET %0h.", d2h.d_data);
          aes_output[31:0] <= d2h.d_data;
          fsm <= {1'b1, AES_DATA_OUT_1_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_OUT_1_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_OUT_1_OFFSET};
        end
        if (count == 3) begin
          // $display("AES_DATA_OUT_1_OFFSET %0h.", d2h.d_data);
          aes_output[63:32] <= d2h.d_data;
          fsm <= {1'b1, AES_DATA_OUT_2_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_OUT_2_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_OUT_2_OFFSET};
        end
        if (count == 3) begin
          // $display("AES_DATA_OUT_2_OFFSET %0h.", d2h.d_data);
          aes_output[95:64] <= d2h.d_data;
          fsm <= {1'b1, AES_DATA_OUT_3_OFFSET};
          count <= 32'b0;
        end
      end

      if (fsm == {1'b1, AES_DATA_OUT_3_OFFSET}) begin
        if (count == 0) begin
          h2d.a_address <= {25'b0, AES_DATA_OUT_3_OFFSET};
        end
        if (count == 3) begin
          // $display("AES_DATA_OUT_3_OFFSET %0h.", d2h.d_data);
          aes_output[127:96] <= d2h.d_data;
          fsm <= 8'hFF;
          count <= 32'b0;
          test_done_o <= 1'b1;
        end
      end

      if (fsm == 8'hFF) begin
        // $display("aes_key    %h", aes_key);
        // $display("aes_input  %h", aes_input);
        // $display("aes_output %h", aes_output);
        test_done_o <= 1'b1;
      end

      if (count > 32'hFF) begin
        test_done_o <= 1'b1;
      end
    end

    // $display("Loop %0d.", count);
    // $display("h2d.a_data %0d.", h2d.a_data);
  end


endmodule


