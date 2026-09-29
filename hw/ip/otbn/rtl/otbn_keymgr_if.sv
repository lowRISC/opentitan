// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN - Keymgr interface
 *
 * This implements the app interface on the OTBN which allows the keymgr to use OTBN as a hashing
 * engine.
 */
module otbn_keymgr_if
  import otbn_pkg::*;
(
  input  logic clk_i,
  input  logic rst_ni,

  // Keymgr app interface
  input  kmac_pkg::app_req_t keymgr_app_i,
  output kmac_pkg::app_rsp_t keymgr_app_o,

  // CSR write
  input  logic        ispr_keymgr_ctrl_wr_i,
  input  logic [31:0] ispr_keymgr_ctrl_wdata_i,

  // CSR read
  output logic [31:0] ispr_keymgr_status_rdata_o,

  // WSR write
  input  logic               ispr_keymgr_msg_s0_l_wr_i,
  input  logic [ExtWLEN-1:0] ispr_keymgr_msg_s0_l_wdata_i,
  input  logic               ispr_keymgr_msg_s0_h_wr_i,
  input  logic [ExtWLEN-1:0] ispr_keymgr_msg_s0_h_wdata_i,
  input  logic               ispr_keymgr_msg_s1_l_wr_i,
  input  logic [ExtWLEN-1:0] ispr_keymgr_msg_s1_l_wdata_i,
  input  logic               ispr_keymgr_msg_s1_h_wr_i,
  input  logic [ExtWLEN-1:0] ispr_keymgr_msg_s1_h_wdata_i,

  // WSR read
  input  logic               ispr_keymgr_msg_s0_l_rd_i,
  output logic [ExtWLEN-1:0] ispr_keymgr_msg_s0_l_rdata_o,
  output logic [ExtWLEN-1:0] ispr_keymgr_msg_s0_h_rdata_o,
  output logic [ExtWLEN-1:0] ispr_keymgr_msg_s1_l_rdata_o,
  output logic [ExtWLEN-1:0] ispr_keymgr_msg_s1_h_rdata_o,

  // Secure wipe
  input  logic               sec_wipe_running_i,
  input  logic               sec_wipe_ispr_keymgr_msg_s0_l_i,
  input  logic               sec_wipe_ispr_keymgr_msg_s0_h_i,
  input  logic               sec_wipe_ispr_keymgr_msg_s1_l_i,
  input  logic               sec_wipe_ispr_keymgr_msg_s1_h_i,
  input  logic [UrndLen-1:0] urnd_data_i,

  // Errors
  output logic sec_wipe_err_o,
  output logic reg_intg_violation_err_o,
  output logic state_err_o
);

  // Encoding generated at commit ba91dd5f17 using Python 3.12.14 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 394079310 --distance 3 --states 6 --bits 6
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (53.33%)
  //  4: ||||||||||||||| (40.00%)
  //  5: || (6.67%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int OtbnKeymgrStateWidth = 6;
  typedef enum logic [OtbnKeymgrStateWidth-1:0] {
    OtbnKeymgrIdle            = 6'b111110,
    OtbnKeymgrReceiving       = 6'b100111,
    OtbnKeymgrResponsePending = 6'b001101,
    OtbnKeymgrSendingResponse = 6'b010001,
    OtbnKeymgrSecWipeDone     = 6'b101000,
    OtbnKeymgrTerminalError   = 6'b000010
  } otbn_keymgr_state_e;

  // Types and signals for CSRs / WSRs
  typedef struct packed {
    logic msg_complete;
    logic msg_valid;
    logic sending;
    logic receiving;
  } keymgr_status_t;

  typedef struct packed {
    logic [32-4-1:0] rsvd;
    logic            send_error;
    logic            rsvd_cmd;
    logic            send;
    logic            start;
  } ispr_keymgr_ctrl_t;

  localparam int unsigned StatusW = $bits(keymgr_status_t);
  localparam int unsigned StrbOffsetW = 16;
  localparam int unsigned StatusRsvdW = 32 - kmac_pkg::MsgStrbW - StrbOffsetW;

  typedef struct packed {
    logic [StatusRsvdW-1:0]         rsvd2;
    logic [kmac_pkg::MsgStrbW-1:0]  strb;
    logic [StrbOffsetW-StatusW-1:0] rsvd1;
    keymgr_status_t                 status;
  } ispr_keymgr_status_t;

  // CSR signals
  logic status_msg_valid_d, status_msg_valid_q;
  logic is_error_rsp_d, is_error_rsp_q;
  logic [kmac_pkg::MsgStrbW-1:0] keymgr_strb_d, keymgr_strb_q;

  // WSR signals
  otbn_wide_intg_word_t ispr_keymgr_msg_s0_l_q, ispr_keymgr_msg_s0_l_d;
  otbn_wide_intg_word_t ispr_keymgr_msg_s0_h_q, ispr_keymgr_msg_s0_h_d;
  otbn_wide_intg_word_t ispr_keymgr_msg_s1_l_q, ispr_keymgr_msg_s1_l_d;
  otbn_wide_intg_word_t ispr_keymgr_msg_s1_h_q, ispr_keymgr_msg_s1_h_d;

  /////////
  // FSM //
  /////////
  otbn_keymgr_state_e state_d, state_q;

  logic accept_msg;
  logic accept_rsp_cmd;
  logic rsp_sent;

  logic msg_accepted;
  logic last_msg_accepted;
  logic is_last_msg;

  logic start_cmd;
  logic rsp_cmd_received;
  logic send_cmd;
  logic send_error_cmd;
  logic send_rsp;

  logic status_msg_complete;
  logic status_receiving;
  logic status_sending;
  logic clear_status;

  logic sec_wipe_detected;
  logic sec_wipe_complete;

  logic fsm_state_error;

  always_comb begin
    state_d = state_q;

    accept_msg       = 1'b0;
    accept_rsp_cmd   = 1'b0;
    send_rsp         = 1'b0;

    is_error_rsp_d = 1'b0;

    status_receiving    = 1'b0;
    status_msg_complete = 1'b0;
    status_sending      = 1'b0;
    clear_status        = 1'b0;
    sec_wipe_complete   = 1'b0;

    fsm_state_error = 1'b0;

    unique case (state_q)
      OtbnKeymgrIdle: begin
        // We do not immediately accept interface request when the start command is issued to avoid
        // factoring the insn path into the ready.
        if (start_cmd) begin
          state_d = OtbnKeymgrReceiving;
        end

        // If a secure wipe happens, never start a session.
        if (sec_wipe_detected) begin
          state_d = OtbnKeymgrSecWipeDone;
        end
      end
      OtbnKeymgrReceiving: begin
        status_receiving = 1'b1;

        // Accept a message when the WSR is free or drain any incoming message during secure wipe.
        accept_msg = !status_msg_valid_q || sec_wipe_detected;

        if (last_msg_accepted) begin
          state_d = OtbnKeymgrResponsePending;
        end
      end
      OtbnKeymgrResponsePending: begin
        status_msg_complete = 1'b1;

        accept_rsp_cmd = 1'b1;
        // If a command is issued, the response is sent in the next state for timing reasons.
        // Otherwise the insn path is factored into the valid and ready path to/from keymgr.
        // During a secure wipe any response is an error response, see below.
        if (rsp_cmd_received || sec_wipe_detected) begin
          is_error_rsp_d = send_error_cmd;
          state_d        = OtbnKeymgrSendingResponse;
        end
      end
      OtbnKeymgrSendingResponse: begin
        status_msg_complete = 1'b1;
        status_sending      = 1'b1;

        // Send the commanded response. During a secure wipe any response is an error response,
        // see below, so no need to update flop as well.
        send_rsp       = 1'b1;
        is_error_rsp_d = is_error_rsp_q;

        if (rsp_sent) begin
          state_d = sec_wipe_detected ? OtbnKeymgrSecWipeDone : OtbnKeymgrIdle;
          // Clear any status holding state (like valid and start command bits)
          clear_status = 1'b1;
        end
      end
      OtbnKeymgrSecWipeDone: begin
        // Wait until any secure wipe has finished. This could also be the next secure wipe.
        if (!sec_wipe_running_i) begin
          state_d           = OtbnKeymgrIdle;
          sec_wipe_complete = 1'b1;
        end
      end
      OtbnKeymgrTerminalError: begin
        state_d         = OtbnKeymgrTerminalError;
        fsm_state_error = 1'b1;
      end
      default: begin
        state_d = OtbnKeymgrTerminalError;
      end
    endcase
  end

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, otbn_keymgr_state_e, OtbnKeymgrIdle)

  ///////////////////////
  // Command detection //
  ///////////////////////
  ispr_keymgr_ctrl_t keymgr_ctrl;
  assign keymgr_ctrl = ispr_keymgr_ctrl_wdata_i;

  // Detect the start command
  assign start_cmd = ispr_keymgr_ctrl_wr_i && keymgr_ctrl.start;

  // Detect the issued response commands
  assign send_cmd         = ispr_keymgr_ctrl_wr_i && keymgr_ctrl.send;
  assign send_error_cmd   = ispr_keymgr_ctrl_wr_i && keymgr_ctrl.send_error;
  assign rsp_cmd_received = (send_cmd || send_error_cmd) && accept_rsp_cmd;

  logic unused_keymgr_ctrl;
  assign unused_keymgr_ctrl = ^{keymgr_ctrl.rsvd, keymgr_ctrl.rsvd_cmd};

  //////////////////////////
  // Message accept logic //
  //////////////////////////
  // Handle the incoming requests
  assign msg_accepted      = keymgr_app_i.req_valid && accept_msg;
  assign is_last_msg       = keymgr_app_i.req_valid && keymgr_app_i.req_last;
  assign last_msg_accepted = is_last_msg && msg_accepted;

  // Handshake request
  assign keymgr_app_o.req_ready = msg_accepted;

  // This is the write enable for the flops capturing the actual data. Only capture the message
  // data if no secure wipe is running.
  logic capture_msg;
  assign capture_msg = msg_accepted && !sec_wipe_detected;

  logic msg_is_read;
  assign msg_is_read = ispr_keymgr_msg_s0_l_rd_i;

  // Set and keep once a request arrives until it is read. A new request has priority over a
  // simultaneous read.
  assign status_msg_valid_d =
      sec_wipe_running_i || clear_status ? 1'b0 : ((status_msg_valid_q && !msg_is_read) ||
                                                   capture_msg);

  // Capture the strobe info when accepting a message but only if not wiping. The message data is
  // captured in a WSR, see below.
  assign keymgr_strb_d = sec_wipe_running_i || clear_status ? '0                :
                         capture_msg                        ? keymgr_app_i.strb : keymgr_strb_q;

  /////////////////////////
  // Response generation //
  /////////////////////////
  // Check the integrity when sending the response. Any error will set the error flag. Suppress
  // the integrity error if a secure wipe is ongoing. Otherwise a recoverable error triggering a
  // secure wipe can be converted to a fatal error if the response is sent before SW did set a
  // proper value (WSRs do not have valid integrity after power on; there is no reset).
  logic [3:0][BaseWordsPerWLEN-1:0][1:0] rsp_data_intg_errs;
  logic rsp_intg_error;
  assign rsp_intg_error = |rsp_data_intg_errs && send_rsp && !sec_wipe_detected;

  // Send the response
  // Note, a secure wipe is allowed to clear the WSRs even when a response is pending. This can
  // violate the valid locked-in principle. But this is a rare edge case and we always assert the
  // error flag as well (which is theoretically also violation). However, this will just result in
  // a failed KDF and both OTBN and keymgr can still return back to idle.
  assign keymgr_app_o.rsp_valid = send_rsp;
  assign keymgr_app_o.error     = is_error_rsp_q || sec_wipe_detected || rsp_intg_error;
  // A static app interface never sends a finish response.
  assign keymgr_app_o.rsp_finish = 1'b0;

  assign rsp_sent = keymgr_app_o.rsp_valid && keymgr_app_i.rsp_ready;

  // Response data path
  logic [WLEN-1:0] rsp_data_s0_l, rsp_data_s0_h;
  logic [WLEN-1:0] rsp_data_s1_l, rsp_data_s1_h;

  for (genvar word = 0; word < BaseWordsPerWLEN; word++) begin : g_rsp_data
    assign rsp_data_s0_l[word * 32 +: 32] = ispr_keymgr_msg_s0_l_q[word].word;
    assign rsp_data_s0_h[word * 32 +: 32] = ispr_keymgr_msg_s0_h_q[word].word;
    assign rsp_data_s1_l[word * 32 +: 32] = ispr_keymgr_msg_s1_l_q[word].word;
    assign rsp_data_s1_h[word * 32 +: 32] = ispr_keymgr_msg_s1_h_q[word].word;

    prim_secded_inv_39_32_dec u_intg_check_msg_s0_l (
      .data_i    (ispr_keymgr_msg_s0_l_q[word]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rsp_data_intg_errs[0][word])
    );
    prim_secded_inv_39_32_dec u_intg_check_msg_s0_h (
      .data_i    (ispr_keymgr_msg_s0_h_q[word]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rsp_data_intg_errs[1][word])
    );
    prim_secded_inv_39_32_dec u_intg_check_msg_s1_l (
      .data_i    (ispr_keymgr_msg_s1_l_q[word]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rsp_data_intg_errs[2][word])
    );
    prim_secded_inv_39_32_dec u_intg_check_msg_s1_h (
      .data_i    (ispr_keymgr_msg_s1_h_q[word]),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rsp_data_intg_errs[3][word])
    );
  end

  // TODO: this always exposes the current WSR content to the interface. A write to the WSRs thus
  // propagates the new values directly to the wires. I think this is ok, but:
  // - Do we need a blanker? But this would add FI attack surface.
  // - Do we need to expose URND when not sending a response?
  //   - Could this be used to measure the URND stream? Do we need a permutation?
  assign keymgr_app_o.digest_s0 = {rsp_data_s0_h, rsp_data_s0_l};
  assign keymgr_app_o.digest_s1 = {rsp_data_s1_h, rsp_data_s1_l};

  ////////////////
  // CSR access //
  ////////////////
  ispr_keymgr_status_t ispr_keymgr_status;
  keymgr_status_t keymgr_status;

  assign keymgr_status = '{
    msg_complete: status_msg_complete,
    msg_valid:    status_msg_valid_q,
    sending:      status_sending,
    receiving:    status_receiving
  };

  assign ispr_keymgr_status = '{
    rsvd2:  '0,
    strb:   keymgr_strb_q,
    rsvd1:  '0 ,
    status: keymgr_status
  };

  assign ispr_keymgr_status_rdata_o = ispr_keymgr_status;

  ////////////////
  // WSR access //
  ////////////////
  // URND data used to wipe the WSRs during a secure wipe.
  otbn_ispr_urnd_t ispr_urnd;
  logic unused_urnd;
  assign ispr_urnd   = urnd_data_i;
  assign unused_urnd = ^ispr_urnd.rsvd;

  otbn_wide_intg_word_t wipe_data;
  assign wipe_data = ispr_urnd.urnd;

  otbn_wide_intg_word_t ispr_keymgr_msg_s0_l_wdata;
  assign ispr_keymgr_msg_s0_l_wdata = ispr_keymgr_msg_s0_l_wdata_i;

  // Compute integrity for received message
  otbn_base_intg_word_t [1:0] rcvd_msg;

  prim_secded_inv_39_32_enc u_intg_req_msg_l (
    .data_i(keymgr_app_i.data_s0[31:0]),
    .data_o(rcvd_msg[0])
  );

  prim_secded_inv_39_32_enc u_intg_req_msg_h (
    .data_i(keymgr_app_i.data_s0[63:32]),
    .data_o(rcvd_msg[1])
  );

  // The received data is always unshared.
  logic unused_data_s1;
  assign unused_data_s1 = ^keymgr_app_i.data_s1;

  // MUX the keymgr message with a write instruction for the lowest two word. The message has
  // priority over the WSR write. A secure wipe has the highest priority so do not accept data from
  // the interface whilst a secure wipe is ongoing. The secure wipe clears the WSRs sequentially.
  for (genvar word = 0; word < BaseWordsPerWLEN; word++) begin : g_wsr
    if (word < 2) begin: g_msg_update
      assign ispr_keymgr_msg_s0_l_d[word] =
          sec_wipe_ispr_keymgr_msg_s0_l_i ? wipe_data[word]                  :
          capture_msg                     ? rcvd_msg[word]                   :
          ispr_keymgr_msg_s0_l_wr_i       ? ispr_keymgr_msg_s0_l_wdata[word] :
                                            ispr_keymgr_msg_s0_l_q[word];
    end else begin : g_insn_only
      assign ispr_keymgr_msg_s0_l_d[word] =
        sec_wipe_ispr_keymgr_msg_s0_l_i ? wipe_data[word]                  :
        ispr_keymgr_msg_s0_l_wr_i       ? ispr_keymgr_msg_s0_l_wdata[word] :
                                          ispr_keymgr_msg_s0_l_q[word];
    end
  end

  // The other WSRs are only accessible via WSR writes.
  assign ispr_keymgr_msg_s0_h_d = sec_wipe_ispr_keymgr_msg_s0_h_i ? wipe_data                    :
                                  ispr_keymgr_msg_s0_h_wr_i       ? ispr_keymgr_msg_s0_h_wdata_i :
                                                                    ispr_keymgr_msg_s0_h_q;

  assign ispr_keymgr_msg_s1_l_d = sec_wipe_ispr_keymgr_msg_s1_l_i ? wipe_data                    :
                                  ispr_keymgr_msg_s1_l_wr_i       ? ispr_keymgr_msg_s1_l_wdata_i :
                                                                    ispr_keymgr_msg_s1_l_q;

  assign ispr_keymgr_msg_s1_h_d = sec_wipe_ispr_keymgr_msg_s1_h_i ? wipe_data                    :
                                  ispr_keymgr_msg_s1_h_wr_i       ? ispr_keymgr_msg_s1_h_wdata_i :
                                                                    ispr_keymgr_msg_s1_h_q;

  assign ispr_keymgr_msg_s0_l_rdata_o = ispr_keymgr_msg_s0_l_q;
  assign ispr_keymgr_msg_s0_h_rdata_o = ispr_keymgr_msg_s0_h_q;
  assign ispr_keymgr_msg_s1_l_rdata_o = ispr_keymgr_msg_s1_l_q;
  assign ispr_keymgr_msg_s1_h_rdata_o = ispr_keymgr_msg_s1_h_q;

  ///////////////////////////
  // Secure wipe detection //
  ///////////////////////////
  logic sec_wipe_detected_d, sec_wipe_detected_q;

  // Factor out complete signal to avoid potential loops.
  assign sec_wipe_detected = sec_wipe_running_i || sec_wipe_detected_q;

  assign sec_wipe_detected_d = sec_wipe_running_i ? 1'b1 :
                               sec_wipe_complete  ? 1'b0 :
                                                    sec_wipe_detected_q;

  ///////////
  // Flops //
  ///////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      status_msg_valid_q   <= '0;
      keymgr_strb_q        <= '0;
      is_error_rsp_q       <= '0;
      sec_wipe_detected_q  <= '0;
    end else begin
      status_msg_valid_q   <= status_msg_valid_d;
      keymgr_strb_q        <= keymgr_strb_d;
      is_error_rsp_q       <= is_error_rsp_d;
      sec_wipe_detected_q  <= sec_wipe_detected_d;
    end
  end

  // Non-resettable WSRs
  always_ff @(posedge clk_i) begin
    ispr_keymgr_msg_s0_l_q <= ispr_keymgr_msg_s0_l_d;
    ispr_keymgr_msg_s0_h_q <= ispr_keymgr_msg_s0_h_d;
    ispr_keymgr_msg_s1_l_q <= ispr_keymgr_msg_s1_l_d;
    ispr_keymgr_msg_s1_h_q <= ispr_keymgr_msg_s1_h_d;
  end

  ////////////////////
  // Error handling //
  ////////////////////
  // There may be no WSR wipe request if no secure wipe is running.
  assign sec_wipe_err_o = !sec_wipe_running_i &&
                          (sec_wipe_ispr_keymgr_msg_s0_l_i || sec_wipe_ispr_keymgr_msg_s0_h_i ||
                           sec_wipe_ispr_keymgr_msg_s1_l_i || sec_wipe_ispr_keymgr_msg_s1_h_i);

  assign reg_intg_violation_err_o = rsp_intg_error;
  assign state_err_o = fsm_state_error;

endmodule
