// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * OTBN's interface to the KMAC HWIP dynamic application interface.
 *
 * This module manages how OTBN SW can interact with the OTBN-KMAC interface. The interface is
 * controlled via CSRs and the message / digest is exchanged via WSRs. The SW then can issue the
 * KMAC commands (START, PROCESS, DONE, the RUN command is implicitly triggered if required) via
 * CSRs and this module translates it to the corresponding app interface requests. The returning
 * responses are translated and exposed via CSRs.
 *
 *                                                                      OTBN  | KMAC HWIP
 *                                                                            |
 *                                                                            |     +----------+
 * +---------+    +---------+         +-----------------------+   app_req_o   |     |          |
 * |  CSRs   |--->|   FSM   |<---+--->| Request generator     |---------------|---->|          |
 * +---------+    +---------+    |    +-----------------------+               |     |          |
 *      |                        |                ^                           |     |          |
 *      |                        |                |                           |     |          |
 * +---------+                   |    +-----------------------+               |     |          |
 * | OTBN SW |<---------------------->| Message / Digest WSRs |               |     |  App IF  |
 * +---------+                   |    +-----------------------+               |     |          |
 *                               |                ^                           |     |          |
 *                               |                |                           |     |          |
 *                               |    +-----------------------+   app_rsp_i   |     |          |
 *                               +--->| Data response handler |<--+-----------|-----|          |
 *                               |    +-----------------------+   |           |     |          |
 *                               |                                |           |     +----------+
 *                               |    +-----------------------+   |           |
 *                               +--->| Termination handler   |<--+           |
 *                                    +-----------------------+               |
 *                                                                            |
 */
module otbn_kmac_if
  import otbn_pkg::*;
(
  input  logic clk_i,
  input  logic rst_ni,

  // KMAC app interface
  output kmac_pkg::app_req_t app_req_o,
  input  kmac_pkg::app_rsp_t app_rsp_i,

  // CSR write
  input  logic        ispr_kmac_status_wr_i,
  input  logic [31:0] ispr_kmac_status_wdata_i,
  input  logic        ispr_kmac_ctrl_wr_i,
  input  logic [31:0] ispr_kmac_ctrl_wdata_i,
  input  logic        ispr_kmac_cfg_wr_i,
  input  logic [31:0] ispr_kmac_cfg_wdata_i,
  input  logic        ispr_kmac_strb_wr_i,
  input  logic [31:0] ispr_kmac_strb_wdata_i,

  // CSR read
  output logic [31:0] ispr_kmac_status_rdata_o,
  output logic [31:0] ispr_kmac_cfg_rdata_o,
  output logic [31:0] ispr_kmac_strb_rdata_o,

  // WSR write
  input  logic               ispr_kmac_data_s0_wr_i,
  input  logic [ExtWLEN-1:0] ispr_kmac_data_s0_wdata_i,
  input  logic               ispr_kmac_data_s1_wr_i,
  input  logic [ExtWLEN-1:0] ispr_kmac_data_s1_wdata_i,

  // WSR read
  input  logic               ispr_kmac_data_s0_rd_i,
  output logic [ExtWLEN-1:0] ispr_kmac_data_s0_rdata_o,
  input  logic               ispr_kmac_data_s1_rd_i,
  output logic [ExtWLEN-1:0] ispr_kmac_data_s1_rdata_o,

  // Secure wipe
  input  logic               sec_wipe_running_i,
  input  logic               sec_wipe_ispr_kmac_data_s0_i,
  input  logic               sec_wipe_ispr_kmac_data_s1_i,
  input  logic [UrndLen-1:0] urnd_data_i,

  // Errors
  output logic sec_wipe_err_o,
  output logic reg_intg_violation_err_o,
  output logic state_err_o
);

  // Encoding generated at commit 7791207ad2 using Python 3.12.13 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 2147904016 --distance 3 --states 12 --bits 8
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||| (27.27%)
  //  4: |||||||||||||||||||| (33.33%)
  //  5: ||||||||||||| (22.73%)
  //  6: |||||||| (13.64%)
  //  7: | (3.03%)
  //  8: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 7
  //
  localparam int OtbnKmacStateWidth = 8;
  typedef enum logic [OtbnKmacStateWidth-1:0] {
    OtbnKmacIdle            = 8'b10010110,
    OtbnKmacStarting        = 8'b11011111,
    OtbnKmacWaitForMsg      = 8'b00000010,
    OtbnKmacSendingMsg      = 8'b01010101,
    OtbnKmacProcessing      = 8'b00001001,
    OtbnKmacReceiving       = 8'b10110001,
    OtbnKmacTerminating     = 8'b00111010,
    OtbnKmacWaitForFinish   = 8'b01101101,
    OtbnKmacWaitForClose    = 8'b11001000,
    OtbnKmacTerminalError   = 8'b11110100,
    OtbnKmacSecWipeClearing = 8'b11000011,
    OtbnKmacSecWipeDone     = 8'b11101110
  } otbn_kmac_state_e;

  typedef enum logic [1:0] {
    ReqDataCfg = 2'b00,
    ReqDataMsg = 2'b01,
    ReqDataOff = 2'b10
  } otbn_kmac_req_data_sel_e;

  typedef struct packed {
    logic close;
    logic done;
    logic proc;
    logic send;
    logic start;
  } kmac_cmd_t;

  typedef struct packed {
    kmac_pkg::app_mode_e        mode;
    sha3_pkg::keccak_strength_e kstrength;
    logic                       en_xof;
  } kmac_cfg_t;

  typedef struct packed {
    logic msg_write_error;
    logic ctrl_error;
    logic rsp_error;
    logic rsp_valid;
    logic ready;
  } kmac_status_t;

  // KMAC_CTRL only holds the command bits, the remaining bits are reserved.
  localparam int unsigned CtrlRsvdW = 32 - $bits(kmac_cmd_t);

  typedef struct packed {
    logic [CtrlRsvdW-1:0] rsvd;
    kmac_cmd_t            cmd;
  } ispr_kmac_ctrl_t;

  // KMAC_CFG holds the session configuration. The fields are doubled for redundancy. The offset is
  // there to start the upper fields at a power of two bit position (makes SW simpler to read).
  localparam int unsigned CfgW       = $bits(kmac_cfg_t);
  localparam int unsigned CfgOffsetW = 16;

  typedef struct packed {
    logic [31-CfgOffsetW-CfgW:0] rsvd_upper;
    kmac_cfg_t                   cfg_upper;
    logic [CfgOffsetW-CfgW-1:0]  rsvd_lower;
    kmac_cfg_t                   cfg_lower;
  } ispr_kmac_cfg_t;

  typedef struct packed {
    logic [31-$bits(kmac_status_t):0] rsvd;
    kmac_status_t                     status;
  } ispr_kmac_status_t;

  // CSR signals
  logic [31:0] kmac_strb_q;
  logic [31:0] kmac_strb_d;

  // WSR signals
  otbn_wide_intg_word_t ispr_kmac_data_s0_q, ispr_kmac_data_s0_d;
  otbn_wide_intg_word_t ispr_kmac_data_s1_q, ispr_kmac_data_s1_d;

  /////////
  // FSM //
  /////////
  otbn_kmac_state_e state_d, state_q;

  kmac_cmd_t current_cmd;
  logic status_ready;

  otbn_kmac_req_data_sel_e req_data_sel;
  logic clear_msg_selector;

  logic send_start_req, start_req_sent;

  logic send_msg;
  logic send_msg_beat;
  logic msg_sent;
  logic no_more_msg_allowed_set;
  logic no_more_msg_allowed_clear;
  logic no_more_msg_allowed_q, no_more_msg_allowed_d;

  logic send_process_req, process_req_sent;
  logic send_termination_req, termination_req_sent;

  logic accept_data_rsp;
  logic clear_rsp_valid;
  logic clear_error_flags;
  logic discard_rsp_ready;
  logic finish_rsp_hs;

  logic sec_wipe_detected;
  logic wipe_configuration;
  logic sec_wipe_complete;

  logic unexpected_cmd_detected;
  logic fsm_state_error;

  always_comb begin
    state_d = state_q;

    // Control signals for requests.
    req_data_sel              = ReqDataOff;
    send_start_req            = 1'b0;
    clear_msg_selector        = 1'b0;
    send_msg                  = 1'b0;
    no_more_msg_allowed_clear = 1'b0;
    send_process_req          = 1'b0;
    send_termination_req      = 1'b0;

    // Control signals for the response handling.
    accept_data_rsp   = 1'b0;
    clear_rsp_valid   = 1'b0;
    clear_error_flags = 1'b0;
    discard_rsp_ready = 1'b0;

    // Secure wipe recovery
    wipe_configuration     = 1'b0;
    sec_wipe_complete      = 1'b0;

    fsm_state_error = 1'b0;

    // The ready signal for the interface checked by SW. Is 1 when the interface is ready to:
    // - Accept a new configuration or start a session when in Idle.
    // - Accept a new message / strobe in the WSRs when in the message phase.
    // - Ready to accept the DONE command once the process command is issued.
    status_ready = state_q inside {OtbnKmacIdle, OtbnKmacWaitForMsg, OtbnKmacReceiving};

    // Detect any command which is out of order. Per default no command is expected.
    unexpected_cmd_detected = |current_cmd;

    unique case (state_q)
      OtbnKmacIdle: begin
        if (current_cmd.start) begin
          state_d = OtbnKmacStarting;
        end
        unexpected_cmd_detected = |{current_cmd.proc, current_cmd.send, current_cmd.done,
                                    current_cmd.close};
        // If a secure wipe is detected, do not start a session and clean the state.
        if (sec_wipe_detected) begin
          state_d = OtbnKmacSecWipeClearing;
        end
      end
      OtbnKmacStarting: begin
        send_start_req            = 1'b1;
        req_data_sel              = ReqDataCfg;
        no_more_msg_allowed_clear = 1'b1;

        if (start_req_sent) begin
          // Immediately end the message phase after the session is started if a secure wipe
          // happened. We must send the start request if it was already pending, otherwise a valid
          // would be dropped. We do not track if a request was pending, so always send it.
          state_d = sec_wipe_detected ? OtbnKmacProcessing : OtbnKmacWaitForMsg;
        end
      end
      OtbnKmacWaitForMsg: begin
        if (sec_wipe_detected) begin
          // Immediately end the message phase.
          state_d = OtbnKmacProcessing;
        end else if (current_cmd.send && !no_more_msg_allowed_q) begin
          // Start to send a message part when the SEND command is issued. But we may only do this
          // if no partial message beat has already been sent. There may be only one partial
          // message beat which must be the last message beat.
          state_d            = OtbnKmacSendingMsg;
          clear_msg_selector = 1'b1;
        end else if (current_cmd.proc) begin
          state_d = OtbnKmacProcessing;
        end
        // There may not be any send command once a partial message was sent. SEND and PROCESS may
        // not be issued simultaneously.
        unexpected_cmd_detected = (|{current_cmd.start, current_cmd.done, current_cmd.close}) ||
                                  (no_more_msg_allowed_q && current_cmd.send)                 ||
                                  (current_cmd.send && current_cmd.proc);
      end
      OtbnKmacSendingMsg: begin
        send_msg     = 1'b1;
        req_data_sel = ReqDataMsg;

        // A secure wipe is allowed to clear KMAC_DATA_Sx even while a message beat is in flight.
        // This can violate the valid locked-in principle. But this is a rare edge case and
        // unstable data just results in garbage digest. The KMAC core can still be returned back
        // to idle. And as any digest is anyway discarded when a secure wipe happens we accept this
        // violation.
        if (msg_sent) begin
          // Immediately end the message phase if secure wipe is ongoing.
          state_d = sec_wipe_detected ? OtbnKmacProcessing : OtbnKmacWaitForMsg;
        end
      end
      OtbnKmacProcessing: begin
        // The message phase is ended and the tracker is cleared that it is always cleared when
        // the session ends.
        no_more_msg_allowed_clear = 1'b1;

        // Send the process request.
        send_process_req = 1'b1;
        req_data_sel     = ReqDataOff; // Selects strobe = '0 which indicates a process request.
        if (process_req_sent) begin
          // The process command must be sent in both the regular and secure wipe case. But we
          // immediately terminate the session if a secure wipe is ongoing.
          state_d = sec_wipe_detected ? OtbnKmacTerminating : OtbnKmacReceiving;
        end
      end
      OtbnKmacReceiving: begin
        accept_data_rsp = 1'b1;
        if (sec_wipe_detected) begin
          // Do not update WSRs anymore and terminate the session immediately.
          accept_data_rsp = 1'b0;
          state_d         = OtbnKmacTerminating;
        end else if (current_cmd.done) begin
          // Continue to accept the currently pending response as controlling the ready directly
          // with the DONE command would factor the insn decoding into the ready timing path. The
          // data and error flag are still updated so all errors are captured.
          state_d         = OtbnKmacTerminating;
          clear_rsp_valid = 1'b1;
        end
        unexpected_cmd_detected = |{current_cmd.start, current_cmd.send, current_cmd.proc,
                                    current_cmd.close};
      end
      OtbnKmacTerminating: begin
        // Do not accept any pending response anymore. The next state will wait for the
        // finish response. The termination request must be sent in both the regular and secure
        // wipe case.
        send_termination_req = 1'b1;
        if (termination_req_sent) begin
          state_d = OtbnKmacWaitForFinish;
        end
      end
      OtbnKmacWaitForFinish: begin
        // Discard any in-flight responses until the finish response arrives.
        discard_rsp_ready = 1'b1;
        if (finish_rsp_hs) begin
          // The session is now terminated on the KMAC side. Now wait for SW to check the response.
          // In case of a secure wipe, we skip the CLOSE command and begin to clear the remaining
          // state.
          state_d = sec_wipe_detected ? OtbnKmacSecWipeClearing : OtbnKmacWaitForClose;
        end
      end
      OtbnKmacWaitForClose: begin
        // Wait until SW has checked the finish response for errors and ends the session.
        // In case of a secure wipe skip the CLOSE command because no SW is active anymore.
        if (sec_wipe_detected) begin
          state_d = OtbnKmacSecWipeClearing;
        end else if (current_cmd.close) begin
          // Clean up any state
          state_d           = OtbnKmacIdle;
          clear_rsp_valid   = 1'b1;
          clear_error_flags = 1'b1;
        end
        unexpected_cmd_detected = |{current_cmd.start, current_cmd.send, current_cmd.proc,
                                    current_cmd.done};
      end
      OtbnKmacSecWipeClearing: begin
        state_d = OtbnKmacSecWipeDone;

        // Clear any configuration values and sending logic. The data WSRs are wiped directly via
        // sec_wipe_ispr_kmac_data_sx_i controlled by otbn_start_stop.
        wipe_configuration        = 1'b1;
        clear_msg_selector        = 1'b1;
        no_more_msg_allowed_clear = 1'b1;
      end
      OtbnKmacSecWipeDone: begin
        // Wait until any secure wipe has finished. This could also be the next secure wipe.
        if (!sec_wipe_running_i) begin
          state_d           = OtbnKmacIdle;
          sec_wipe_complete = 1'b1;
        end
      end
      OtbnKmacTerminalError: begin
        state_d         = OtbnKmacTerminalError;
        fsm_state_error = 1'b1;
      end
      default: begin
        state_d = OtbnKmacTerminalError;
      end
    endcase
  end

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, otbn_kmac_state_e, OtbnKmacIdle)

  //////////////////////
  // Message selector //
  //////////////////////
  localparam int unsigned MsgParts  = WLEN / kmac_pkg::MsgWidth;
  localparam int unsigned MsgPartsW = prim_util_pkg::vbits(MsgParts);

  logic [MsgPartsW-1:0] msg_beat_idx;

  logic [kmac_pkg::MsgWidth-1:0] req_msg_s0, req_msg_s1;
  logic [kmac_pkg::MsgStrbW-1:0] req_msg_strb;
  otbn_base_intg_word_t          req_msg_intg_s0[2];
  otbn_base_intg_word_t          req_msg_intg_s1[2];

  // Select the 64-bit word of the message WSRs which gets sent as next.
  // The integrity of the selected word is checked when the data is sent.
  assign req_msg_intg_s0[0] = ispr_kmac_data_s0_q[msg_beat_idx * 2 + 0];
  assign req_msg_intg_s0[1] = ispr_kmac_data_s0_q[msg_beat_idx * 2 + 1];
  assign req_msg_intg_s1[0] = ispr_kmac_data_s1_q[msg_beat_idx * 2 + 0];
  assign req_msg_intg_s1[1] = ispr_kmac_data_s1_q[msg_beat_idx * 2 + 1];

  assign req_msg_s0 = {req_msg_intg_s0[1].word, req_msg_intg_s0[0].word};
  assign req_msg_s1 = {req_msg_intg_s1[1].word, req_msg_intg_s1[0].word};

  // Select the corresponding strobe.
  assign req_msg_strb = kmac_strb_q[8 * msg_beat_idx +: 8];

  // Integrity check for message parts
  logic [7:0] req_msg_intg_violation_errors;
  logic       req_msg_intg_violation_error_raw;

  assign req_msg_intg_violation_error_raw = |req_msg_intg_violation_errors;

  prim_secded_inv_39_32_dec u_intg_check_msg_s0_w0 (
    .data_i    (req_msg_intg_s0[0]),
    .data_o    (),
    .syndrome_o(),
    .err_o     (req_msg_intg_violation_errors[1:0])
  );

  prim_secded_inv_39_32_dec u_intg_check_msg_s0_w1 (
    .data_i    (req_msg_intg_s0[1]),
    .data_o    (),
    .syndrome_o(),
    .err_o     (req_msg_intg_violation_errors[3:2])
  );

  prim_secded_inv_39_32_dec u_intg_check_msg_s1_w0 (
    .data_i    (req_msg_intg_s1[0]),
    .data_o    (),
    .syndrome_o(),
    .err_o     (req_msg_intg_violation_errors[5:4])
  );

  prim_secded_inv_39_32_dec u_intg_check_msg_s1_w1 (
    .data_i    (req_msg_intg_s1[1]),
    .data_o    (),
    .syndrome_o(),
    .err_o     (req_msg_intg_violation_errors[7:6])
  );

  ////////////////////////
  // Request generation //
  ////////////////////////
  kmac_pkg::app_ses_config_t app_cfg_s0, app_cfg_s1;
  logic [kmac_pkg::MsgWidth-1:0] req_data_s0, req_data_s1;
  logic [kmac_pkg::MsgStrbW-1:0] req_strb;
  logic msg_beat_is_partial;
  logic msg_beat_is_empty;
  logic is_last_msg_beat;
  logic msg_beat_sent;
  logic end_msg_phase;

  // Request data and strobe selection
  // For area and FI reasons we always forward the data WSR bits except when sending the
  // configuration. The muxing is limited to the actual config bits. This makes it harder to inject
  // deterministic data. At most an adversary could glitch the configuration bits to something
  // deterministic, but not the entire data beat. We send the configuration on both shares for
  // redundancy.
  always_comb begin
    req_data_s0 = req_msg_s0;
    req_data_s1 = req_msg_s1;

    if (req_data_sel == ReqDataCfg) begin
      req_data_s0[$bits(kmac_pkg::app_ses_config_t) - 1:0] = app_cfg_s0;
      req_data_s1[$bits(kmac_pkg::app_ses_config_t) - 1:0] = app_cfg_s1;
    end
  end

  // The strobe is relevant when sending the message and must be '0 for the process request. Its
  // value does not matter when sending the configuration request or commands.
  assign req_strb = req_data_sel == ReqDataMsg ? req_msg_strb : '0;

  // A counter to step through the message beats of the current message part in the WSRs.
  logic cnt_state_error;
  logic cnt_commit;
  prim_count #(
    .Width(MsgPartsW),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Incr)
  ) u_msg_selector_count (
    .clk_i,
    .rst_ni,
    .clr_i             (clear_msg_selector),
    .set_i             (1'b0),
    .set_cnt_i         ('0),
    .incr_en_i         (1'b1),
    .decr_en_i         (1'b0),
    .step_i            (MsgPartsW'('d1)),
    .commit_i          (cnt_commit),
    .cnt_o             (msg_beat_idx),
    .cnt_after_commit_o(),
    .err_o             (cnt_state_error)
  );

  // Commit the counter update if:
  // - The counter must be cleared (clear must be committed).
  // - A message beat is sent.
  assign cnt_commit = clear_msg_selector || msg_beat_sent;

  // Start command is sent once handshake occurred.
  assign start_req_sent = send_start_req & app_rsp_i.req_ready;

  // Sending a message consists of sending 64-bit message parts in up to 4 message beats.
  // The last message beat can be partial. OTBN does not set the last flag in this case. OTBN SW
  // must always end the message phase by issuing a PROCESS command which will send an empty
  // message with the last flag asserted.
  // If the current message beat is empty, we do not place a message request and end the sending.
  // If a secure wipe happens, we only send the current message beat and then end the sending.
  assign msg_beat_is_partial = ~(&req_strb); // An empty message is also consider as partial.
  assign msg_beat_is_empty   = ~(|req_strb);
  assign is_last_msg_beat    = (msg_beat_idx == MsgPartsW'(MsgParts - 1)) || msg_beat_is_partial ||
                               sec_wipe_detected;

  assign send_msg_beat = send_msg && !msg_beat_is_empty;
  assign end_msg_phase = send_msg && msg_beat_is_empty;

  assign msg_beat_sent = send_msg_beat && app_rsp_i.req_ready;
  assign msg_sent      = (msg_beat_sent && is_last_msg_beat) || end_msg_phase;

  // Track when a partial message was sent because now SW may not send any more data. Note an empty
  // message is also considered as partial. An empty message is however never sent to the
  // interface but still marks the end of the message phase.
  assign no_more_msg_allowed_set = msg_sent && msg_beat_is_partial;

  assign no_more_msg_allowed_d = no_more_msg_allowed_set   ? 1'b1 :
                                 no_more_msg_allowed_clear ? 1'b0 :
                                                             no_more_msg_allowed_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      no_more_msg_allowed_q <= 1'b0;
    end else begin
      no_more_msg_allowed_q <= no_more_msg_allowed_d;
    end
  end

  // Integrity is only checked when message data is exposed to interface.
  logic req_msg_intg_violation_error;
  assign req_msg_intg_violation_error =
      req_msg_intg_violation_error_raw && (req_data_sel == ReqDataMsg) && app_req_o.req_valid;

  // Process command is sent once handshake occurred.
  assign process_req_sent = send_process_req & app_rsp_i.req_ready;

  // Done command is sent once termination request handshake occurred.
  assign termination_req_sent = send_termination_req & app_rsp_i.req_ready;

  ///////////////////////
  // Response handling //
  ///////////////////////
  logic rsp_valid_q, rsp_valid_d;

  logic data_rsp_ready;
  logic data_rsp_hs;

  logic response_wr;
  logic [kmac_pkg::DynAppDigestW-1:0] response_s0;
  logic [kmac_pkg::DynAppDigestW-1:0] response_s1;

  logic data_s0_pending_d, data_s0_pending_q;
  logic data_s1_pending_d, data_s1_pending_q;
  logic data_consumed;

  logic discarded_rsp_hs;

  // The data is consumed when both shares have been read or when a pending response is read in
  // this cycle. The read control signals are predecoded and thus have minimal impact on the ready
  // timing path.
  assign data_consumed = (!data_s0_pending_q || ispr_kmac_data_s0_rd_i) &&
                         (!data_s1_pending_q || ispr_kmac_data_s1_rd_i);

  // Accept the next response when the FSM allows it and the current response has been or is being
  // consumed by the current instruction.
  assign data_rsp_ready = data_consumed && accept_data_rsp;

  assign data_rsp_hs = app_rsp_i.rsp_valid && data_rsp_ready;

  // Forward the response to the WSR write logic when accepting the next response.
  assign response_wr = data_rsp_hs;
  assign response_s0 = app_rsp_i.digest_s0[kmac_pkg::DynAppDigestW-1:0];
  assign response_s1 = app_rsp_i.digest_s1[kmac_pkg::DynAppDigestW-1:0];

  // The dynamic app interface only sends valid data on the lower bits.
  logic unused_digest;
  assign unused_digest = ^{app_rsp_i.digest_s0[kmac_pkg::AppDigestW-1:kmac_pkg::DynAppDigestW],
                           app_rsp_i.digest_s1[kmac_pkg::AppDigestW-1:kmac_pkg::DynAppDigestW]};

  // Keep track of whether the current digest data has been consumed. The handshake has priority to
  // enable accepting the next response in the same cycle as the current data is read.
  // We discard any pending tracking when leaving the receive phase (when rsp_valid is cleared).
  assign data_s0_pending_d = clear_rsp_valid        ? 1'b0 :
                             data_rsp_hs            ? 1'b1 :
                             ispr_kmac_data_s0_rd_i ? 1'b0 :
                                                      data_s0_pending_q;

  assign data_s1_pending_d = clear_rsp_valid        ? 1'b0 :
                             data_rsp_hs            ? 1'b1 :
                             ispr_kmac_data_s1_rd_i ? 1'b0 :
                                                      data_s1_pending_q;

  // Discard any incoming responses until the finish response arrives.
  assign discarded_rsp_hs = app_rsp_i.rsp_valid && discard_rsp_ready;

  // Detect the finish response.
  assign finish_rsp_hs = discarded_rsp_hs && app_rsp_i.rsp_finish;

  ////////////////////
  // Status updates //
  ////////////////////
  logic wsr_write_detected;
  logic wsr_write_collision;

  logic rsp_error_q, rsp_error_d;
  logic msg_write_error_q, msg_write_error_d;
  logic ctrl_error_q, ctrl_error_d;

  logic clear_rsp_error;
  logic clear_msg_write_error;
  logic clear_ctrl_error;

  // Handshakes have priority over consumption to enable same cycle updates. The consumption may
  // only be relevant while accepting digest responses. Discard any updates during the secure wipe
  // except when FSM resets the flag.
  assign rsp_valid_d = wipe_configuration               ? 1'b0        :
                       sec_wipe_detected                ? rsp_valid_q :
                       clear_rsp_valid                  ? 1'b0        :
                       finish_rsp_hs || data_rsp_hs     ? 1'b1        :
                       data_consumed && accept_data_rsp ? 1'b0        :
                                                          rsp_valid_q;

  // The RSP_ERROR is sticky and W1C where any response has priority over the SW clearing.
  // Discard any updates during the secure wipe except when FSM resets the flag.
  assign rsp_error_d = wipe_configuration              ? 1'b0                           :
                       sec_wipe_detected               ? rsp_error_q                    :
                       data_rsp_hs || discarded_rsp_hs ? app_rsp_i.error || rsp_error_q :
                       clear_rsp_error                 ? 1'b0                           :
                                                         rsp_error_q;

  // The MSG_WRITE_ERROR is sticky and W1C.
  logic msg_write_error_detected;
  assign msg_write_error_detected = (wsr_write_detected && !status_ready) || wsr_write_collision ||
                                    (ispr_kmac_strb_wr_i && !status_ready) ||
                                    (ispr_kmac_cfg_wr_i && !status_ready);

  assign msg_write_error_d = wipe_configuration       ? 1'b0 :
                             msg_write_error_detected ? 1'b1 :
                             clear_msg_write_error    ? 1'b0 :
                                                        msg_write_error_q;

  // The CTRL_ERROR is sticky and W1C.
  assign ctrl_error_d = wipe_configuration      ? 1'b0 :
                        unexpected_cmd_detected ? 1'b1 :
                        clear_ctrl_error        ? 1'b0 :
                                                  ctrl_error_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rsp_valid_q       <= 1'b0;
      data_s0_pending_q <= 1'b0;
      data_s1_pending_q <= 1'b0;
      rsp_error_q       <= 1'b0;
      msg_write_error_q <= 1'b0;
      ctrl_error_q      <= 1'b0;
    end else begin
      rsp_valid_q       <= rsp_valid_d;
      data_s0_pending_q <= data_s0_pending_d;
      data_s1_pending_q <= data_s1_pending_d;
      rsp_error_q       <= rsp_error_d;
      msg_write_error_q <= msg_write_error_d;
      ctrl_error_q      <= ctrl_error_d;
    end
  end

  ////////////////
  // CSR access //
  ////////////////
  // KMAC_CTRL
  ispr_kmac_ctrl_t ispr_kmac_ctrl_w;
  logic unused_ctrl_w;

  assign ispr_kmac_ctrl_w = ispr_kmac_ctrl_wdata_i;
  assign unused_ctrl_w    = ^ispr_kmac_ctrl_w.rsvd;

  // Extract command from write.
  assign current_cmd = ispr_kmac_ctrl_w.cmd & {$bits(kmac_cmd_t){ispr_kmac_ctrl_wr_i}};

  // KMAC_CFG
  ispr_kmac_cfg_t ispr_kmac_cfg_w;
  ispr_kmac_cfg_t ispr_kmac_cfg_r;
  logic unused_cfg_w;
  kmac_cfg_t kmac_cfg_q[2];
  kmac_cfg_t kmac_cfg_d[2];

  assign ispr_kmac_cfg_w = ispr_kmac_cfg_wdata_i;
  assign unused_cfg_w    = ^{ispr_kmac_cfg_w.rsvd_lower, ispr_kmac_cfg_w.rsvd_upper};
  assign ispr_kmac_cfg_r = '{
    rsvd_upper: '0,
    cfg_upper:  kmac_cfg_q[1],
    rsvd_lower: '0,
    cfg_lower:  kmac_cfg_q[0]
  };
  assign ispr_kmac_cfg_rdata_o = ispr_kmac_cfg_r;

  // Capture writes to configuration bits. This is explicitly wiped by the FSM to avoid wiping the
  // configuration in case a start request is pending when a secure wipe starts. The configuration
  // bits are doubled for redundancy.
  assign kmac_cfg_d[0] = wipe_configuration ? '0                        :
                         ispr_kmac_cfg_wr_i ? ispr_kmac_cfg_w.cfg_lower :
                                              kmac_cfg_q[0];
  assign kmac_cfg_d[1] = wipe_configuration ? '0                        :
                         ispr_kmac_cfg_wr_i ? ispr_kmac_cfg_w.cfg_upper :
                                              kmac_cfg_q[1];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      kmac_cfg_q <= '{default: kmac_cfg_t'('0)};
    end else begin
      kmac_cfg_q <= kmac_cfg_d;
    end
  end

  // Cast current configuration to KMAC app specific session config. We need helper signals as
  // directly using kmac_cfg_q[0].member does not work for a packed array.
  kmac_cfg_t kmac_cfg_s0, kmac_cfg_s1;
  assign kmac_cfg_s0 = kmac_cfg_q[0];
  assign kmac_cfg_s1 = kmac_cfg_q[1];

  assign app_cfg_s0 = '{
    en_xof:      kmac_cfg_s0.en_xof,
    kstrength:   kmac_cfg_s0.kstrength,
    mode:        kmac_cfg_s0.mode,
    prefix_mode: 1'b0 // not relevant
  };

  assign app_cfg_s1 = '{
    en_xof:      kmac_cfg_s1.en_xof,
    kstrength:   kmac_cfg_s1.kstrength,
    mode:        kmac_cfg_s1.mode,
    prefix_mode: 1'b0 // not relevant
  };

  // KMAC_STRB
  assign ispr_kmac_strb_rdata_o = kmac_strb_q;

  assign kmac_strb_d = wipe_configuration  ? '0                     :
                       ispr_kmac_strb_wr_i ? ispr_kmac_strb_wdata_i :
                                             kmac_strb_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      kmac_strb_q <= '0;
    end else begin
      kmac_strb_q <= kmac_strb_d;
    end
  end

  // KMAC_STATUS
  ispr_kmac_status_t ispr_kmac_status_w;
  ispr_kmac_status_t ispr_kmac_status_r;
  logic unused_status_w;

  assign ispr_kmac_status_w = ispr_kmac_status_wdata_i;
  assign unused_status_w    = ^{ispr_kmac_status_w.rsvd,
                                ispr_kmac_status_w.status.ready,
                                ispr_kmac_status_w.status.rsp_valid};
  assign ispr_kmac_status_r = '{
    rsvd: '0,
    status: '{
      msg_write_error: msg_write_error_q,
      ctrl_error:      ctrl_error_q,
      rsp_error:       rsp_error_q,
      rsp_valid:       rsp_valid_q,
      ready:           status_ready
    }
  };

  assign ispr_kmac_status_rdata_o = ispr_kmac_status_r;

  assign clear_rsp_error = (ispr_kmac_status_w.status.rsp_error && ispr_kmac_status_wr_i) ||
                           clear_error_flags;

  assign clear_msg_write_error =
      (ispr_kmac_status_w.status.msg_write_error && ispr_kmac_status_wr_i) || clear_error_flags;

  assign clear_ctrl_error = (ispr_kmac_status_w.status.ctrl_error && ispr_kmac_status_wr_i) ||
                            clear_error_flags;

  ///////////////////////////
  // Secure wipe detection //
  ///////////////////////////
  logic sec_wipe_detected_d, sec_wipe_detected_q;

  // Factor out complete signal to avoid potential loops.
  assign sec_wipe_detected = sec_wipe_running_i || sec_wipe_detected_q;

  assign sec_wipe_detected_d = sec_wipe_running_i ? 1'b1 :
                               sec_wipe_complete  ? 1'b0 :
                                                    sec_wipe_detected_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sec_wipe_detected_q <= '0;
    end else begin
      sec_wipe_detected_q <= sec_wipe_detected_d;
    end
  end

  ////////////////
  // WSR access //
  ////////////////
  // URND data used to wipe the KMAC_DATA_Sx WSRs during a secure wipe.
  otbn_ispr_urnd_t ispr_urnd;
  logic unused_urnd;
  assign ispr_urnd   = urnd_data_i;
  assign unused_urnd = ^ispr_urnd.rsvd;

  assign ispr_kmac_data_s0_rdata_o = ispr_kmac_data_s0_q;
  assign ispr_kmac_data_s1_rdata_o = ispr_kmac_data_s1_q;

  // Compute the integrity for the digest responses from the KMAC interface.
  otbn_base_intg_word_t [1:0] response_intg_s0;
  otbn_base_intg_word_t [1:0] response_intg_s1;

  prim_secded_inv_39_32_enc u_intg_rsp_data_s0_w0 (
    .data_i(response_s0[31:0]),
    .data_o(response_intg_s0[0])
  );

  prim_secded_inv_39_32_enc u_intg_rsp_data_s0_w1 (
    .data_i(response_s0[63:32]),
    .data_o(response_intg_s0[1])
  );

  prim_secded_inv_39_32_enc u_intg_rsp_data_s1_w0 (
    .data_i(response_s1[31:0]),
    .data_o(response_intg_s1[0])
  );

  prim_secded_inv_39_32_enc u_intg_rsp_data_s1_w1 (
    .data_i(response_s1[63:32]),
    .data_o(response_intg_s1[1])
  );

  // The regular write data for KMAC_DATA_Sx.
  otbn_wide_intg_word_t ispr_kmac_data_s0_wdata;
  otbn_wide_intg_word_t ispr_kmac_data_s1_wdata;

  assign ispr_kmac_data_s0_wdata = ispr_kmac_data_s0_wdata_i;
  assign ispr_kmac_data_s1_wdata = ispr_kmac_data_s1_wdata_i;

  // MUX the KMAC response with a write instruction for the lowest two word. The response has
  // priority over the WSR write. A secure wipe has the highest priority. The secure wipe clears
  // the two WSRs sequentially.
  otbn_wide_intg_word_t wipe_data;
  assign wipe_data = ispr_urnd.urnd;

  for (genvar word = 0; word < BaseWordsPerWLEN; word++) begin : g_wsr
    if (word < 2) begin : g_rsp_update
      assign ispr_kmac_data_s0_d[word] =
          sec_wipe_ispr_kmac_data_s0_i ? wipe_data[word]               :
          response_wr                  ? response_intg_s0[word]        :
          ispr_kmac_data_s0_wr_i       ? ispr_kmac_data_s0_wdata[word] :
                                         ispr_kmac_data_s0_q[word];
      assign ispr_kmac_data_s1_d[word] =
          sec_wipe_ispr_kmac_data_s1_i ? wipe_data[word]               :
          response_wr                  ? response_intg_s1[word]        :
          ispr_kmac_data_s1_wr_i       ? ispr_kmac_data_s1_wdata[word] :
                                         ispr_kmac_data_s1_q[word];
    end else begin : g_insn_only
      assign ispr_kmac_data_s0_d[word] =
          sec_wipe_ispr_kmac_data_s0_i ? wipe_data[word]               :
          ispr_kmac_data_s0_wr_i       ? ispr_kmac_data_s0_wdata[word] :
                                         ispr_kmac_data_s0_q[word];
      assign ispr_kmac_data_s1_d[word] =
          sec_wipe_ispr_kmac_data_s1_i ? wipe_data[word]               :
          ispr_kmac_data_s1_wr_i       ? ispr_kmac_data_s1_wdata[word] :
                                         ispr_kmac_data_s1_q[word];
    end
  end

  // Detect when an instruction writes to the data WSRs.
  assign wsr_write_detected = ispr_kmac_data_s0_wr_i || ispr_kmac_data_s1_wr_i;

  // Detect when an instruction write collides with a response.
  assign wsr_write_collision = response_wr && wsr_write_detected;

  // Non-resettable WSR data store. Wiped during secure wipe.
  always_ff @(posedge clk_i) begin
    ispr_kmac_data_s0_q <= ispr_kmac_data_s0_d;
    ispr_kmac_data_s1_q <= ispr_kmac_data_s1_d;
  end

  //////////////////////////
  // Interface connection //
  //////////////////////////
  assign app_req_o = '{
    req_valid: send_start_req || send_msg_beat || send_process_req || send_termination_req,
    data_s0:   req_data_s0,
    data_s1:   req_data_s1,
    strb:      req_strb,
    req_last:  send_process_req || send_termination_req,
    rsp_ready: data_rsp_ready || discard_rsp_ready
  };

  // Assert that only one request source  is active at the same time as otherwise requests are
  // colliding.
  `ASSERT(OnlyOneReqSourceActive_A,
      $onehot0({send_start_req, send_msg_beat, send_process_req, send_termination_req}))

  // There may only happen one response handshake simultaneously.
  `ASSERT(OnlyOneRspHandshake_A, $onehot0({data_rsp_hs, finish_rsp_hs}))
  // There may only be one receiver active at the same time.
  `ASSERT(OnlyOneReceiverActive_A, $onehot0({data_rsp_ready, discard_rsp_ready}))

  ////////////////////
  // Error handling //
  ////////////////////
  // There may be no WSR wipe request if no secure wipe is running.
  assign sec_wipe_err_o = !sec_wipe_running_i &&
                          (sec_wipe_ispr_kmac_data_s0_i || sec_wipe_ispr_kmac_data_s1_i);

  assign reg_intg_violation_err_o = req_msg_intg_violation_error;
  assign state_err_o              = fsm_state_error || cnt_state_error;

endmodule
