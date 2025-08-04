// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES wrapper for FI experiments

module aes_wrap
  import aes_pkg::*;
#(
  parameter bit         AES192Enable = 1,           // Can be 0 (disable), or 1 (enable).
  parameter bit         SecMasking   = 1,           // Can be 0 (no masking), or
                                                    // 1 (first-order masking) of the cipher
                                                    // core. Masking requires the use of a
                                                    // masked S-Box, see SBoxImpl parameter.
                                                    // Note: currently, constant masks are
                                                    // used, this is of course not secure.
  parameter sbox_impl_e SecSBoxImpl  = SBoxImplDom  // See aes_pkg.sv
) (
  input  logic         clk_i,
  input  logic         rst_ni,

  input  logic [127:0] aes_input,
  input  logic [255:0] aes_key,
  output logic [127:0] aes_output,

  output logic         alert_recov_o,
  output logic         alert_fatal_o,

  output logic         test_done_o
);

  localparam logic SIDELOAD = 1'b1;
  localparam aes_mode_e AES_MODE = AES_ECB;

  import aes_pkg::*;
  import aes_reg_pkg::*;
  import tlul_pkg::*;

  logic unused_idle;
  logic [31:0] unused_wdata;
  logic edn_req;
  keymgr_pkg::hw_key_req_t keymgr_key;
  tl_h2d_t h2d, h2d_intg; // req
  tl_d2h_t d2h; // rsp
  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx;
  prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx;

  // Sideload interface - allows for quicker simulation.
  assign keymgr_key.valid = 1'b1;
  assign keymgr_key.key[0][255:0] = aes_key;
  assign keymgr_key.key[1][255:0] = '0;

  // Alert receivers
  assign alert_rx[0].ping_p = 1'b0;
  assign alert_rx[0].ping_n = 1'b1;
  assign alert_rx[0].ack_p  = 1'b0;
  assign alert_rx[0].ack_n  = 1'b1;
  assign alert_rx[1].ping_p = 1'b0;
  assign alert_rx[1].ping_n = 1'b1;
  assign alert_rx[1].ack_p  = 1'b0;
  assign alert_rx[1].ack_n  = 1'b1;

  // Alert transceivers
  assign alert_recov_o = alert_tx[0].alert_p | ~alert_tx[0].alert_n;
  assign alert_fatal_o = alert_tx[1].alert_p | ~alert_tx[1].alert_n;

  // Command integrity generation
  tlul_cmd_intg_gen tlul_cmd_intg_gen (
    .tl_i(h2d),
    .tl_o(h2d_intg)
  );

  // Data integrity generation
  prim_secded_inv_39_32_enc u_data_gen (
    .data_i (h2d.a_data),
    .data_o ({h2d_intg.a_user.data_intg, unused_wdata})
  );

  // DUT
  aes #(
    .AES192Enable(AES192Enable),
    .SecMasking(SecMasking),
    .SecSBoxImpl(SecSBoxImpl)
  ) aes (
    .clk_i           (clk_i),
    .rst_ni          (rst_ni),
    .rst_shadowed_ni (rst_ni),
    .idle_o          (unused_idle),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .clk_edn_i       (clk_i),
    .rst_edn_ni      (rst_ni),
    .edn_o           (edn_req),
    .edn_i           ({edn_req, 1'b1, 32'h12345678}),
    .keymgr_key_i    (keymgr_key),
    .tl_i            (h2d_intg),
    .tl_o            (d2h),
    .alert_rx_i      (alert_rx),
    .alert_tx_o      (alert_tx)
  );

  // FSM
  localparam int StateWidth = BlockAw;
  typedef enum logic [StateWidth-1:0] {
    IDLE,
    W_KEY_SHARE0_0,
    W_KEY_SHARE0_1,
    W_KEY_SHARE0_2,
    W_KEY_SHARE0_3,
    W_KEY_SHARE0_4,
    W_KEY_SHARE0_5,
    W_KEY_SHARE0_6,
    W_KEY_SHARE0_7,
    W_KEY_SHARE1_0,
    W_KEY_SHARE1_1,
    W_KEY_SHARE1_2,
    W_KEY_SHARE1_3,
    W_KEY_SHARE1_4,
    W_KEY_SHARE1_5,
    W_KEY_SHARE1_6,
    W_KEY_SHARE1_7,
    W_IV_0,
    W_IV_1,
    W_IV_2,
    W_IV_3,
    W_DATA_IN_0,
    W_DATA_IN_1,
    W_DATA_IN_2,
    W_DATA_IN_3,
    R_DATA_OUT_0,
    R_DATA_OUT_1,
    R_DATA_OUT_2,
    R_DATA_OUT_3,
    W_CTRL_SHADOWED,
    W_CTRL_AUX_SHADOWED,
    W_TRIGGER_OFFSET,
    R_STATUS,
    FINISH
  } aes_wrap_ctrl_e;
  aes_wrap_ctrl_e aes_wrap_ctrl_ns, aes_wrap_ctrl_cs;
  logic [31:0] count_d, count_q;
  logic [127:0] data_out_d, data_out_q;

  always_comb begin : aes_wrap_fsm
    // TL-UL
    h2d.a_valid           = 1'b0;
    h2d.a_opcode          = PutFullData;
    h2d.a_param           = 3'h0;                      // static
    h2d.a_size            = 2'h2;                      // static
    h2d.a_source          = 8'h0;                      // static
    h2d.a_address         = 32'hAAAAAAA8;
    h2d.a_mask            = 4'hF;                      // static
    h2d.a_data            = 32'h55555555;
    h2d.a_user.rsvd       = '0;                        // static
    h2d.a_user.instr_type = prim_mubi_pkg::MuBi4False; // static (Data)
    h2d.a_user.cmd_intg   = '0;                        // will be driven by tlul_cmd_intg_gen
    h2d.a_user.data_intg  = '0;                        // will be driven by prim_secded_enc
    h2d.d_ready           = 1'b1;                      // static

    // FSM
    aes_wrap_ctrl_ns      = aes_wrap_ctrl_cs;
    count_d               = count_q + 32'h1;
    data_out_d            = data_out_q;
    test_done_o           = 1'b0;

    unique case (aes_wrap_ctrl_cs)

      IDLE: begin
        // Poll the status register until the DUT has finished initialization and becomes idle.
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = Get;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_STATUS_OFFSET};

        if (d2h.d_valid) begin
          h2d.a_valid = 1'b0;
          if (d2h.d_data[0] == 1'b1) begin
            // Once the DUT is idle, we can start the configuration sequence and clear the counter.
            aes_wrap_ctrl_ns = W_CTRL_AUX_SHADOWED;
            count_d          = 32'h0;
          end
        end
      end

      W_CTRL_AUX_SHADOWED: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_CTRL_AUX_SHADOWED_OFFSET};
        h2d.a_data    = 32'h0;

        // We can't do back to back transactions. De-assert valid while receiving response.
        if (d2h.d_valid) begin
          h2d.a_valid = 1'b0;
        end

        // The shadow reg needs to be written twice.
        if (count_q >= 32'h3 && d2h.d_valid) begin
          aes_wrap_ctrl_ns = W_CTRL_SHADOWED;
        end
      end

      W_CTRL_SHADOWED: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_CTRL_SHADOWED_OFFSET};
        h2d.a_data    = {18'h0, 1'b0 ,1'b0, SIDELOAD, AES_128, AES_MODE, AES_ENC};

        // We can't do back to back transactions. De-assert valid while receiving response.
        if (d2h.d_valid) begin
          h2d.a_valid = 1'b0;
        end

        // The shadow reg needs to be written twice.
        if (count_q >= 32'h7 && d2h.d_valid) begin
          aes_wrap_ctrl_ns = SIDELOAD == 1'b1 ?
              (AES_MODE == AES_ECB ? W_DATA_IN_0 : W_IV_0) : W_KEY_SHARE0_0;
        end
      end

      W_KEY_SHARE0_0: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_0_OFFSET};
        h2d.a_data    = aes_key[31:0];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_1;
        end
      end

      W_KEY_SHARE0_1: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_1_OFFSET};
        h2d.a_data    = aes_key[63:32];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_2;
        end
      end

      W_KEY_SHARE0_2: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_2_OFFSET};
        h2d.a_data    = aes_key[95:64];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_3;
        end
      end

      W_KEY_SHARE0_3: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_3_OFFSET};
        h2d.a_data    = aes_key[127:96];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_4;
        end
      end

      W_KEY_SHARE0_4: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_4_OFFSET};
        h2d.a_data    = aes_key[159:128];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_5;
        end
      end

      W_KEY_SHARE0_5: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_5_OFFSET};
        h2d.a_data    = aes_key[195:160];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_6;
        end
      end

      W_KEY_SHARE0_6: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_6_OFFSET};
        h2d.a_data    = aes_key[227:196];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE0_7;
        end
      end

      W_KEY_SHARE0_7: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE0_7_OFFSET};
        h2d.a_data    = aes_key[255:228];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_0;
        end
      end

      W_KEY_SHARE1_0: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_0_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_1;
        end
      end

      W_KEY_SHARE1_1: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_1_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_2;
        end
      end

      W_KEY_SHARE1_2: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_2_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_3;
        end
      end

      W_KEY_SHARE1_3: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_3_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_4;
        end
      end

      W_KEY_SHARE1_4: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_4_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_5;
        end
      end

      W_KEY_SHARE1_5: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_5_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_6;
        end
      end

      W_KEY_SHARE1_6: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_6_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_KEY_SHARE1_7;
        end
      end

      W_KEY_SHARE1_7: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_KEY_SHARE1_7_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = AES_MODE == AES_ECB ? W_DATA_IN_0 : W_IV_0;
        end
      end

      W_IV_0: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_IV_0_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_IV_1;
        end
      end

      W_IV_1: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_IV_1_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_IV_2;
        end
      end

      W_IV_2: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_IV_2_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_IV_3;
        end
      end

      W_IV_3: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_IV_3_OFFSET};
        h2d.a_data    = '0;
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_DATA_IN_0;
        end
      end

      W_DATA_IN_0: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_IN_0_OFFSET};
        h2d.a_data    = aes_input[31:0];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_DATA_IN_1;
        end
      end

      W_DATA_IN_1: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_IN_1_OFFSET};
        h2d.a_data    = aes_input[63:32];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_DATA_IN_2;
        end
      end

      W_DATA_IN_2: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_IN_2_OFFSET};
        h2d.a_data    = aes_input[95:64];
        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = W_DATA_IN_3;
        end
      end

      W_DATA_IN_3: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = PutFullData;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_IN_3_OFFSET};
        h2d.a_data    = aes_input[127:96];
        if (d2h.d_valid) begin
          // Clear the counter to serve as a reference for the experiments.
          h2d.a_valid      = 1'b0;
          aes_wrap_ctrl_ns = R_STATUS;
          count_d          = '0;
        end
      end

      R_STATUS: begin
        // After providing the last data word, the DUT will start. Poll the status register until
        // the DUT is idle and has valid output data.
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = Get;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_STATUS_OFFSET};

        if (d2h.d_valid) begin
          h2d.a_valid = 1'b0;
          if ((d2h.d_data[0] == 1'b1) && (d2h.d_data[3] == 1'b1)) begin
            aes_wrap_ctrl_ns = R_DATA_OUT_0;
          end
        end
      end

      R_DATA_OUT_0: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = Get;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_OUT_0_OFFSET};

        if (d2h.d_valid) begin
          h2d.a_valid      = 1'b0;
          data_out_d[31:0] = d2h.d_data;
          aes_wrap_ctrl_ns = R_DATA_OUT_1;
        end
      end

      R_DATA_OUT_1: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = Get;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_OUT_1_OFFSET};

        if (d2h.d_valid) begin
          h2d.a_valid       = 1'b0;
          data_out_d[63:32] = d2h.d_data;
          aes_wrap_ctrl_ns  = R_DATA_OUT_2;
        end
      end

      R_DATA_OUT_2: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = Get;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_OUT_2_OFFSET};

        if (d2h.d_valid) begin
          h2d.a_valid       = 1'b0;
          data_out_d[95:64] = d2h.d_data;
          aes_wrap_ctrl_ns  = R_DATA_OUT_3;
        end
      end

      R_DATA_OUT_3: begin
        h2d.a_valid   = 1'b1;
        h2d.a_opcode  = Get;
        h2d.a_address = {{{32-BlockAw}{1'b0}}, AES_DATA_OUT_3_OFFSET};

        if (d2h.d_valid) begin
          h2d.a_valid        = 1'b0;
          data_out_d[127:96] = d2h.d_data;
          aes_wrap_ctrl_ns   = FINISH;
        end
      end

      FINISH: begin
        // Just signal end of simulation.
        test_done_o = 1'b1;
      end

      default: begin
        aes_wrap_ctrl_ns = FINISH;
      end
    endcase // aes_wrap_ctrl_cs

    // We can't handle TL-UL errors. Abort.
    if (d2h.d_valid && d2h.d_error) begin
      aes_wrap_ctrl_ns = FINISH;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : fsm_reg
    if (!rst_ni) begin
      aes_wrap_ctrl_cs <= IDLE;
      count_q          <= 32'b0;
    end else begin
      aes_wrap_ctrl_cs <= aes_wrap_ctrl_ns;
      count_q          <= count_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : data_out_reg
    if (!rst_ni) begin
      data_out_q <= '0;
    end else begin
      data_out_q <= data_out_d;
    end
  end
  assign aes_output = data_out_q;

endmodule
