// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Application interface
//
// This module implements the app interface which arbitrates between the SW interface and up to
// NumAppIntf hardware app interfaces. While a session is active (either an app or SW), other
// requests are stalled.
//
// There are two kind of app interfaces: Static interfaces which have a configuration defined at
// compile-time and only a one-shot digest can be retrieved. A dynamic interface can send the
// desired hashing configuration at run time and supports XOF operation.

`include "prim_assert.sv"

module kmac_app
  import kmac_pkg::*;
#(
  // App specific configs are defined in kmac_pkg
  parameter  bit          EnMasking          = 1'b0,
  localparam int          Share              = (EnMasking) ? 2 : 1, // derived parameter
  parameter  bit          SecIdleAcceptSwMsg = 1'b0,
  parameter  int unsigned NumAppIntf         = 4,
  parameter  app_config_t AppCfg[NumAppIntf] = '{AppCfgKeyMgr, AppCfgLcCtrl,
                                                 AppCfgRomCtrl, AppCfgOtbn}
) (
  input clk_i,
  input rst_ni,

  // Secret Key from register
  input [MaxKeyLen-1:0] reg_key_data_i[Share],
  input key_len_e       reg_key_len_i,

  // Prefix from register
  input [sha3_pkg::NSRegisterSize*8-1:0] reg_prefix_i,

  // mode, strength, kmac_en from register
  input logic                       reg_kmac_en_i,
  input sha3_pkg::sha3_mode_e       reg_sha3_mode_i,
  input sha3_pkg::keccak_strength_e reg_keccak_strength_i,

  // Data from Software
  input                sw_valid_i,
  input [MsgWidth-1:0] sw_data_i,
  input [MsgWidth-1:0] sw_strb_i,
  output logic         sw_ready_o,

  // KeyMgr Sideload Key interface
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // Application Message in/ Digest out interface + control signals
  input  app_req_t [NumAppIntf-1:0] app_i,
  output app_rsp_t [NumAppIntf-1:0] app_o,

  // to KMAC Core: Secret key
  output logic [MaxKeyLen-1:0] key_data_o[Share],
  output key_len_e             key_len_o,
  output logic                 key_valid_o,

  // to MSG_FIFO
  output logic                kmac_valid_o,
  output logic [MsgWidth-1:0] kmac_data_o[Share],
  // This strobe is on bit level for the packer. The FIFO will then convert it again to byte level.
  output logic [MsgWidth-1:0] kmac_strb_o,
  input  logic                kmac_ready_i,
  output logic                kmac_bypass_fifo_o,

  // Signal to KMAC core that a KMAC operation is ongoing.
  output logic kmac_en_o,

  // To Sha3 Core
  output logic [sha3_pkg::NSRegisterSize*8-1:0] sha3_prefix_o,
  output sha3_pkg::sha3_mode_e                  sha3_mode_o,
  output sha3_pkg::keccak_strength_e            keccak_strength_o,

  // The current keccak state from SHA3 Core
  input                        keccak_state_valid_i,
  input [sha3_pkg::StateW-1:0] keccak_state_i[Share],

  // The keccak state is exposed to the STATE TL-window if no application is active. If a key from
  // the KeyMgr is used, the capacity region is zeroed. If an app is active the state reads as
  // zero.
  output logic                        reg_state_valid_o,
  output logic [sha3_pkg::StateW-1:0] reg_state_o[Share],

  // Controls for SW whether to take the key from the KeyMgr sideload interface or registers. For
  // KMAC operations initiated by an app interface, we always take the sideloaded key.
  // If 1, the key for KMAC is taken from the KeyMgr sideload interface.
  // If 0, the key is taken from the registers.
  input logic keymgr_key_en_i,

  // Command from software
  input kmac_cmd_e sw_cmd_i,

  // Status signals from SHA3 core
  input prim_mubi_pkg::mubi4_t absorbed_i,
  input logic                  squeezing_i,

  // to KMAC
  output kmac_cmd_e cmd_o,

  // to SW
  output prim_mubi_pkg::mubi4_t absorbed_o,

  // To status
  output logic app_active_o,

  // The entropy_fast_process bit is forced to 0 when recovering an error state.
  input  logic entropy_fast_process_i,
  output logic entropy_fast_process_o,

  // Entropy must be ready before a KMAC operation can be performed.
  input prim_mubi_pkg::mubi4_t entropy_ready_i,

  // Error input
  // This error comes from KMAC/SHA3 engine and is pulsed if a wrong command sequence is detected
  // or kept high as long as any control signal has an invalid value (e.g. if the done mubi signal
  // is attacked to enforce a known digest value).
  // This error is reported to the ERR_CODE regardless whether app or SW is active.
  input error_i,

  // Pulsed when SW acknowledges error by writing to the err_processed bit. Lets the interface
  // return to idle after errors.
  input err_processed_i,

  output prim_mubi_pkg::mubi4_t clear_after_error_o,

  // Reports error and its type if an FIFO or FSM error occurred.
  output kmac_pkg::err_t error_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Fatal errors
  output logic sparse_fsm_error_o,
  output logic counter_error_o
);

  // Create a lint error to reduce the risk of accidentally enabling this feature.
  `ASSERT_STATIC_LINT_ERROR(KmacSecIdleAcceptSwMsgNonDefault, SecIdleAcceptSwMsg == 0)

  import sha3_pkg::KeccakBitCapacity;
  import sha3_pkg::L128;
  import sha3_pkg::L224;
  import sha3_pkg::L256;
  import sha3_pkg::L384;
  import sha3_pkg::L512;

  /////////////////
  // Definitions //
  /////////////////

  localparam int KeyMgrKeyW = $bits(keymgr_key_i.key[0]);

  localparam key_len_e KeyLengths [5] = '{Key128, Key192, Key256, Key384, Key512};

  localparam int SelKeySize = (AppKeyW == 128) ? 0 :
                              (AppKeyW == 192) ? 1 :
                              (AppKeyW == 256) ? 2 :
                              (AppKeyW == 384) ? 3 :
                              (AppKeyW == 512) ? 4 : 0 ;
  localparam int SelDigSize = (AppDigestW == 128) ? 0 :
                              (AppDigestW == 192) ? 1 :
                              (AppDigestW == 256) ? 2 :
                              (AppDigestW == 384) ? 3 :
                              (AppDigestW == 512) ? 4 : 0 ;
  // Key length is always the same as the full app digest width.
  localparam key_len_e SideloadedKey = KeyLengths[SelKeySize];

  // Define right_encode(outlen) value here
  // Look at kmac_pkg::key_len_e for the kinds of key size
  //
  // These values should be exactly the same as the key length encodings
  // in kmac_core.sv, with the only difference being that the byte representing
  // the byte-length of the encoded value is in the MSB position due to right encoding
  // instead of in the LSB position (left encoding).
  localparam int OutLenW = 24;
  localparam logic [OutLenW-1:0] EncodedOutLen [5]= '{
    24'h 0001_80, // Key128
    24'h 0001_C0, // Key192
    24'h 02_0001, // Key256
    24'h 02_8001, // Key384
    24'h 02_0002  // Key512
  };

  localparam logic [OutLenW-1:0] EncodedOutLenStrb [5] = '{
    24'h 00FFFF, // Key128,
    24'h 00FFFF, // Key192
    24'h FFFFFF, // Key256
    24'h FFFFFF, // Key384
    24'h FFFFFF  // Key512
  };

  /////////////
  // Signals //
  /////////////

  st_e st, st_d;

  logic keymgr_key_used;

  // Response channel signals
  // The state machine controls the datapath mux selection and handles the requests and responses.
  app_rsp_t app_rsp;
  logic app_data_ready, app_req_ready, app_error_req_ready;
  logic app_digest_valid;
  logic app_finish_rsp_valid, app_error_rsp_valid;
  logic app_finish_rsp_is_error;
  logic [AppDigestW-1:0] app_digest[2];

  localparam int unsigned AppIdxW = $clog2(NumAppIntf);

  // app_id indicates, which app interface was chosen. various logic use this
  // value to get the config or return the data.
  logic [AppIdxW-1:0] app_id, app_id_d;
  logic               clr_appid, set_appid;

  // Output length
  logic [OutLenW-1:0] encoded_outlen, encoded_outlen_strb;

  // state output
  // Mux selection signal
  app_mux_sel_e mux_sel;
  app_mux_sel_e mux_sel_buf_output;
  app_mux_sel_e mux_sel_buf_err_check;
  app_mux_sel_e mux_sel_buf_kmac;

  // Tracking and error signals
  kmac_pkg::err_t fsm_err, mux_err;
  logic err_sha3_during_app_set, err_sha3_during_app_d, err_sha3_during_app_q;

  /////////////////////////////
  // Application arbitration //
  /////////////////////////////
  // Latch the selected app ID when FSM grants a request. Per default select ID 0. The FSM and
  // datapath ensure that no data is leaked if interface is not active.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) app_id <= AppIdxW'(0);
    else if (clr_appid) app_id <= AppIdxW'(0);
    else if (set_appid) app_id <= app_id_d;
  end

  // The arbitration uses a fixed priority. The assumption is that the requests normally do no
  // collide. If this assumption doesn't hold anymore, consider RR arbiter.
  logic [NumAppIntf-1:0] app_req_valids;
  logic [$clog2(NumAppIntf)-1:0] arb_idx;
  logic arb_valid;
  logic arb_ready;

  // Pick all request valid signals from the interfaces
  always_comb begin
    app_req_valids = '0;
    for (int unsigned i = 0; i < NumAppIntf; i++) begin
      app_req_valids[i] = app_i[i].req_valid;
    end
  end

  prim_arbiter_fixed #(
    .N (NumAppIntf),
    .DW(1),
    .EnDataPort(1'b 0)
  ) u_appid_arb (
    .clk_i,
    .rst_ni,

    .req_i  (app_req_valids),
    .data_i ('{default:'0}),
    .gnt_o  (), // not used
    .idx_o  (arb_idx),

    .valid_o (arb_valid),
    .data_o  (), // not used
    .ready_i (arb_ready)
  );

  assign app_id_d = AppIdxW'(arb_idx);
  assign arb_ready = set_appid;

  //////////////////////////
  // App config selection //
  //////////////////////////
  // Select the new configuration from either the compile-time defined configuration or from the
  // supplied session configuration. This operates on the non-latched app ID so the configuration
  // can be latched at the same time the ID is.
  app_config_t     app_cfg;
  app_ses_config_t app_ses_cfg_raw;
  app_ses_config_t app_ses_cfg_pending;
  app_ses_config_t app_ses_cfg_d;
  app_ses_config_t app_ses_cfg_q;

  // Note, the parsed value of prefix_mode is not actually used but just here to have a complete
  // type. It is overwritten below.
  assign app_ses_cfg_raw = app_ses_config_t'(app_i[arb_idx].data_s0[$bits(app_ses_config_t)-1:0]);

  always_comb begin
    app_ses_cfg_pending.mode        = AppCfg[arb_idx].session_cfg.mode;
    app_ses_cfg_pending.kstrength   = AppCfg[arb_idx].session_cfg.kstrength;
    app_ses_cfg_pending.en_xof      = AppCfg[arb_idx].session_cfg.en_xof;
    app_ses_cfg_pending.prefix_mode = AppCfg[arb_idx].session_cfg.prefix_mode;

    // Overrule configuration with configuration supplied by dynamic interface.
    if (AppCfg[arb_idx].if_type == AppDynamic) begin
      app_ses_cfg_pending = app_ses_cfg_raw;

      // For KMAC always use prefix defined at compile time. This saves the prefix check.
      // Otherwise use prefix from CSR.
      app_ses_cfg_pending.prefix_mode = app_ses_cfg_pending.mode == AppKMAC ? 1'b1 : 1'b0;
    end
  end

  // KMAC en / SHA3 mode / Strength / configuration latching.
  logic                       kmac_en_d, kmac_en_q;
  sha3_pkg::sha3_mode_e       sha3_mode_d, sha3_mode_q;
  sha3_pkg::keccak_strength_e keccak_strength_d, keccak_strength_q;

  always_comb begin
    app_ses_cfg_d     = app_ses_cfg_q;
    kmac_en_d         = kmac_en_q;
    sha3_mode_d       = sha3_mode_q;
    keccak_strength_d = keccak_strength_q;

    if (clr_appid) begin
      // When an app finishes, latch values from CSRs.
      app_ses_cfg_d     = AppSesCfgDefault;
      kmac_en_d         = reg_kmac_en_i;
      sha3_mode_d       = reg_sha3_mode_i;
      keccak_strength_d = reg_keccak_strength_i;
    end else if (set_appid) begin
      // When an app starts, latch its configuration.
      app_ses_cfg_d     = app_ses_cfg_pending;
      kmac_en_d         = app_ses_cfg_pending.mode == AppKMAC ? 1'b 1 : 1'b 0;
      // KMAC is based upon CShake
      sha3_mode_d       = app_ses_cfg_pending.mode == AppSHA3  ? sha3_pkg::Sha3  :
                          app_ses_cfg_pending.mode == AppShake ? sha3_pkg::Shake : sha3_pkg::CShake;
      keccak_strength_d = app_ses_cfg_pending.kstrength;
    end else if (st == StIdle) begin
      // In idle always propagate the latest CSR values as there is no latch trigger when SW starts
      // a hashing operation.
      app_ses_cfg_d     = AppSesCfgDefault;
      kmac_en_d         = reg_kmac_en_i;
      sha3_mode_d       = reg_sha3_mode_i;
      keccak_strength_d = reg_keccak_strength_i;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      app_ses_cfg_q     <= AppSesCfgDefault;
      kmac_en_q         <= 1'b 0;
      sha3_mode_q       <= sha3_pkg::Sha3;
      keccak_strength_q <= sha3_pkg::L256;
    end else begin
      app_ses_cfg_q     <= app_ses_cfg_d;
      kmac_en_q         <= kmac_en_d;
      sha3_mode_q       <= sha3_mode_d;
      keccak_strength_q <= keccak_strength_d;
    end
  end

  assign kmac_en_o         = kmac_en_q;
  assign sha3_mode_o       = sha3_mode_q;
  assign keccak_strength_o = keccak_strength_q;

  // Force the entropy_fast_process bit to 0 when recovering from error.
  logic disable_entropy_fast_process;
  assign entropy_fast_process_o = disable_entropy_fast_process ? 1'b0 : entropy_fast_process_i;

  // Construct the complete configuration for the active app from the static and latched
  // session configuration.
  always_comb begin
    app_cfg             = AppCfg[app_id];
    app_cfg.session_cfg = app_ses_cfg_q;
  end

  ////////////////////////
  // App config checker //
  ////////////////////////
  logic valid_app_sha3_strength;
  logic valid_app_shake_strength;
  logic valid_app_kmac_cfg;
  logic valid_app_mode_strength_raw;
  logic valid_app_mode_strength;
  logic valid_app_cfg;

  assign valid_app_sha3_strength = app_cfg.session_cfg.kstrength inside {sha3_pkg::L224,
                                                                         sha3_pkg::L256,
                                                                         sha3_pkg::L384,
                                                                         sha3_pkg::L512};

  assign valid_app_shake_strength = app_cfg.session_cfg.kstrength inside {sha3_pkg::L128,
                                                                          sha3_pkg::L256};

  assign valid_app_mode_strength_raw =
      app_cfg.session_cfg.mode == AppSHA3                            ? valid_app_sha3_strength  :
      app_cfg.session_cfg.mode inside {AppShake, AppCShake, AppKMAC} ? valid_app_shake_strength :
                                                                       1'b0;

  // Ignore the mode and strength check if app allows unsupported combinations.
  assign valid_app_mode_strength = valid_app_mode_strength_raw || app_cfg.en_unsup_comb;

  assign valid_app_kmac_cfg = prim_mubi_pkg::mubi4_test_true_strict(entropy_ready_i);

  assign valid_app_cfg = valid_app_mode_strength &&
                         (app_cfg.session_cfg.mode == AppKMAC ? valid_app_kmac_cfg : 1'b1);

  // A compile-time defined configuration must always result in a valid mode-strength
  // configuration.
  `ASSERT(ConfigAlwaysValidIfStatic_A,
          app_active_o && app_cfg.if_type == AppStatic |-> valid_app_mode_strength)

  /////////////////////////////
  // Application Mux / Demux //
  /////////////////////////////
  // The active app's request and response channel is muxed here from / to local signals.
  app_req_t app_req;
  assign app_req = app_i[app_id];

  // There are three ready sources which can accept a request. The app_data_ready active in the
  // message phase and is driven by the FIFO. The app_req_ready is controlled by the FSM to accept
  // the control requests (start/config, process, and termination). The app_error_req_ready is used
  // to accept messages and control requests during the error handling.
  // Similarly, there are three response generators. One drives digest responses, one the finish
  // response and one the error responses.
  assign app_rsp = '{
    req_ready:  app_data_ready | app_error_req_ready | app_req_ready,
    rsp_valid:  app_digest_valid | app_finish_rsp_valid | app_error_rsp_valid,
    digest_s0:  app_digest[0],
    digest_s1:  app_digest[1],
    error:      app_error_rsp_valid | app_finish_rsp_is_error |
                // Must use _d as error is relevant in cycle the digest is returned.
                (err_sha3_during_app_d & app_cfg.if_type == AppStatic),
    rsp_finish: app_finish_rsp_valid
  };

  // The three response generators may never be active at the same time because otherwise responses
  // would collide.
  `ASSERT(AppOnlyOneRspSourceActive_A,
      $onehot0({app_digest_valid, app_finish_rsp_valid, app_error_rsp_valid}))

  always_comb begin
    for (int unsigned i = 0; i < NumAppIntf; i++) begin
      if (i == app_id) begin
        app_o[i] = app_rsp;
      end else begin
        app_o[i] = APP_RSP_DEFAULT;
      end
    end
  end

  /////////
  // FSM //
  /////////
  logic clear_app_trackers;

  logic any_request_outstanding;
  logic last_req_pending;
  logic process_cmd_pending;
  logic last_req_hs;

  logic last_msg_part_received_d, last_msg_part_received_q;
  logic last_msg_part_received_set;

  logic process_cmd_sent_d, process_cmd_sent_q;
  logic process_cmd_sent_set;

  logic pending_digest_rsp_d, pending_digest_rsp_q;
  logic pending_error_rsp_d, pending_error_rsp_q;

  logic digest_parts_available;
  logic squeeze_again;
  logic app_push_digest;
  logic clear_digest_pusher;

  logic service_rejected_error_d, service_rejected_error_q;
  logic service_rejected_error_set;

  logic err_key_used_but_invalid;
  logic err_key_used_but_invalid_set;
  logic err_key_used_but_invalid_clear;
  logic err_key_used_but_invalid_d, err_key_used_but_invalid_q;
  logic err_during_sw_d, err_during_sw_q;
  logic err_during_sw_set;
  logic err_processed_d, err_processed_q;

  // State register
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, st_d, st, st_e, StIdle)

  // Next State & output logic
  // SEC_CM: FSM.SPARSE
  always_comb begin
    st_d = st;

    mux_sel = SecIdleAcceptSwMsg ? SelSw : SelNone;

    // app_id control
    set_appid = 1'b 0;
    clr_appid = 1'b 0;

    // Command towards the KMAC core
    cmd_o = CmdNone;

    // Software output
    absorbed_o = prim_mubi_pkg::MuBi4False;

    // Bypass FIFO if masked app is active.
    kmac_bypass_fifo_o = 1'b0;

    // Ready signal to handshake requests for dynamic interfaces.
    app_req_ready = 1'b0;

    // Control signals for the digest pusher.
    app_push_digest     = 1'b0;
    clear_digest_pusher = 1'b0;

    // Finish response
    app_finish_rsp_valid    = 1'b0;
    app_finish_rsp_is_error = 1'b0;

    // Error tracking and handling
    fsm_err                        = '{valid: 1'b0, code: ErrNone, info: '0};
    sparse_fsm_error_o             = 1'b0;
    clear_after_error_o            = prim_mubi_pkg::MuBi4False;
    service_rejected_error_set     = 1'b0;
    err_sha3_during_app_set        = 1'b0;
    err_key_used_but_invalid_clear = 1'b0;
    process_cmd_sent_set           = 1'b0;
    last_msg_part_received_set     = 1'b0;
    err_during_sw_set              = 1'b0;
    clear_app_trackers             = 1'b0;
    app_error_req_ready            = 1'b0;
    app_error_rsp_valid            = 1'b0;

    disable_entropy_fast_process = 1'b0;

    unique case (st)
      StIdle: begin
        clear_app_trackers = 1'b1;

        if (arb_valid) begin
          // An app was chosen, latch the ID.
          st_d = StAppCfg;
          set_appid = 1'b1;
        end else if (sw_cmd_i == CmdStart) begin
          // Software initiates the sequence
          st_d = StSw;
          cmd_o = CmdStart;
        end
      end

      StAppCfg: begin
        if (!valid_app_cfg) begin
          // Either the entropy source was not marked as ready for a KMAC operation, or the App
          // configuration is invalid, or the configuration in the registers supplied by SW is
          // invalid. In this error case we still go to the "message absorb" phase but no data is
          // forwarded to the actual SHA3 core. This simplifies the error handling on the
          // application side.
          st_d                       = StErrorAwaitMsg;
          service_rejected_error_set = 1'b1;
        end else begin
          // The configuration is valid and also latched. We can now send the start command and
          // begin to absorb the message.
          st_d  = StAppMsg;
          cmd_o = CmdStart;
        end
        // Handshake the configuration request also if there is an error. This is required as an
        // application interface still must send the message.
        // For static interfaces we stall the first request as it already contains data.
        app_req_ready = app_cfg.if_type == AppDynamic;
      end

      StAppMsg: begin
        mux_sel            = SelApp;
        kmac_bypass_fifo_o = app_cfg.masked;

        // Accept any process command immediately and do not forward the request to the message
        // FIFO.
        app_req_ready              = process_cmd_pending;
        last_msg_part_received_set = last_req_hs;

        if (last_req_hs) begin
          if (app_cfg.session_cfg.mode == AppKMAC) begin
            st_d = StAppOutLen;
          end else begin
            st_d = StAppProcess;
          end
        end else if (err_sha3_during_app_q) begin
          // Handshaking last message part has priority as this error is also checked afterwards.
          st_d = StErrorAwaitMsg;
        end
      end

      StAppOutLen: begin
        mux_sel            = SelOutLen;
        kmac_bypass_fifo_o = app_cfg.masked;

        if (kmac_valid_o && kmac_ready_i) begin
          st_d = StAppProcess;
        end else begin
          st_d = StAppOutLen;
        end
      end

      StAppProcess: begin
        cmd_o                = CmdProcess;
        st_d                 = StAppWait;
        // Bypass must be stable until process command has been sent.
        kmac_bypass_fifo_o   = app_cfg.masked;
        process_cmd_sent_set = 1'b1;
      end

      StAppWait: begin
        // absorbed_i is pulsed once when the first process command ends. squeezing_i is high once
        // the processing or subsequent squeezes have finished. This is only relevant for dynamic
        // interfaces.
        if (prim_mubi_pkg::mubi4_test_true_strict(absorbed_i) ||
            (squeezing_i && app_cfg.if_type == AppDynamic)) begin
          st_d                = StAppPushDigest;
          clear_digest_pusher = 1'b1;
        end
      end

      StAppPushDigest: begin
        // Static interface:
        // - Return full digest in one response and return to idle (via finish).
        // Dynamic interface:
        // - Push the available digest / rate in parts.
        // - For SHAKE and CSHAKE, if digest / rate is fully pushed, trigger a squeeze.
        // - End the session if a termination request arrives.
        app_push_digest = 1'b1;

        if (app_cfg.if_type == AppStatic) begin
          if (app_rsp.rsp_valid && app_req.rsp_ready) begin
            // Must be on _d signal to capture the error in the same cycle.
            st_d = err_sha3_during_app_d ? StErrorAwaitSw : StAppFinish;
          end
        end else begin
          // Ending a session by handshaking the request takes priority over 1) handling a SHA3
          // error as it is checked for when sending the response and 2) squeezing to avoid
          // starting an obsolete squeeze operation.
          if (last_req_pending) begin
            st_d          = StAppFinish;
            app_req_ready = 1'b1;
          end else if (err_sha3_during_app_q) begin
            st_d = StErrorPush;
          end else if (squeeze_again && !pending_digest_rsp_d) begin
            // Trigger a squeeze if there should be sent more digest parts. Ensure that there
            // is no pending response which would be 'killed' when changing the state.
            cmd_o = CmdManualRun;
            st_d  = StAppWait;
          end
        end
      end

      StAppFinish: begin
        if (app_cfg.if_type == AppStatic) begin
          // Immediately end the session for static interfaces.
          st_d      = StIdle;
          cmd_o     = CmdDone;
          clr_appid = 1'b1;
        end else begin
          // Await handshake of pending response from last cycle(s) (digest or error response).
          // Otherwise the finish response would violate the valid locked-in principle.
          app_push_digest     = pending_digest_rsp_q;
          app_error_rsp_valid = pending_error_rsp_q;
          if (!pending_digest_rsp_q && !pending_error_rsp_q) begin
            // We now can send the finish response. Send again the error flag to cover the case the
            // error occurred whilst the last digest response was pending.
            app_finish_rsp_valid    = 1'b1;
            app_finish_rsp_is_error = err_sha3_during_app_q;

            // Once the finish response is handshaked the session can be terminated.
            if (app_finish_rsp_valid && app_req.rsp_ready) begin
              st_d      = StIdle;
              cmd_o     = CmdDone;
              clr_appid = 1'b1;
              if (err_sha3_during_app_q) begin
                clear_after_error_o = prim_mubi_pkg::MuBi4True;
              end
            end
         end
        end
      end

      StSw: begin
        mux_sel = SelSw;

        cmd_o = sw_cmd_i;
        absorbed_o = absorbed_i;

        if (sw_cmd_i == CmdDone) begin
          st_d = StIdle;
        end else begin
          st_d = StSw;
        end
      end

      StErrorKeyNotValid: begin
        // Signal the error to SW and start the error recovery. This state won't accept any
        // requests, so we cannot miss the last message request.
        st_d = StErrorAwaitMsg;

        // Clear the error as we now start handling it.
        err_key_used_but_invalid_clear = 1'b1;

        // Report the error to SW.
        fsm_err.valid = 1'b 1;
        fsm_err.code = ErrKeyNotValid;
        fsm_err.info = 24'(app_id);
      end

      StErrorAwaitMsg: begin
        if (err_during_sw_q) begin
          // Only wait for SW to ack the error.
          st_d = StErrorAwaitSw;
        end else begin
          // Track if the last message arrives.
          last_msg_part_received_set = last_req_hs;

          // Once the last message arrived, send error response in next cycle. We must use the _q
          // signal to avoid 1) a timing loop with the ready and 2) handshaking a pending
          // termination request in case we enter this error state after the message has already
          // been received.
          if (last_msg_part_received_q) begin
            st_d = StErrorNotify;
          end else begin
            // Continue to absorb data or a process command on the app interface.
            app_error_req_ready = 1'b1;
          end
        end
      end

      StErrorNotify: begin
        // Send error response back to app. Once response is handshaked, wait for termination
        // request. Static interfaces don't wait for a termination request and skip this state.
        app_error_rsp_valid = 1'b1;

        if (app_rsp.rsp_valid && app_req.rsp_ready) begin
          st_d = app_cfg.if_type == AppDynamic ? StErrorAwaitTermination : StErrorFinish;
        end
      end

      StErrorAwaitTermination: begin
        // A state entered only for dynamic interfaces. Wait for the app to send a termination
        // request.
        if (app_req.req_valid && app_req.req_last) begin
          st_d          = StErrorFinish;
          app_req_ready = 1'b1;
        end
      end

      StErrorFinish: begin
        // Send finish response (dynamic) or exit immediately (static).
        // For service-rejected errors, return to idle without SW interaction.
        // For other errors, wait for SW to acknowledge the error.

        // A SHA3 error can occur after the service rejected error is latched. Thus only send an
        // error-free finish response if the only error case is a service rejected error.
        app_finish_rsp_valid    = app_cfg.if_type == AppDynamic;
        app_finish_rsp_is_error = !service_rejected_error_q || err_sha3_during_app_q;

        if ((app_finish_rsp_valid && app_req.rsp_ready) || (app_cfg.if_type == AppStatic)) begin
          if (!app_finish_rsp_is_error) begin
            clr_appid           = 1'b1;
            clear_after_error_o = prim_mubi_pkg::MuBi4True;
            st_d                = StIdle;
          end else begin
            st_d = StErrorAwaitSw;
          end
        end
      end

      StErrorAwaitSw: begin
        // Wait for SW to have processed the error.
        if (err_processed_q) begin
          // Flush the message FIFO and let the SHA3 engine compute a digest (which won't be used
          // but serves to bring the SHA3 engine back to the idle state). Skip the command if
          // error occurred after regular PROCESS command has been sent and the processing is
          // already ongoing or has already finished. Note, the process command is not tracked
          // during SW operation to have the same behaviour as the KMAC before the extended app
          // interface was added.
          st_d = StErrorAwaitAbsorbed;

          if (!process_cmd_sent_q) begin
            cmd_o = CmdProcess;
          end
        end
      end

      StErrorAwaitAbsorbed: begin
        // Wait until the hashing engine has finished computing the garbage digest. Use the
        // squeezing_i signal to cover the case when the engine finishes before we wait for it.

        if (squeezing_i) begin
          // Clear internal variables, send done command, and return to idle.
          clr_appid           = 1'b1;
          clear_after_error_o = prim_mubi_pkg::MuBi4True;
          cmd_o               = CmdDone;
          st_d                = StIdle;
          // If error originated from SW, report 'absorbed' to SW.
          if (err_during_sw_q) begin
            absorbed_o = prim_mubi_pkg::MuBi4True;
          end
        end
      end

      StErrorPush: begin
        // State for dynamic interfaces only.
        // An error occurred while pushing digest parts. Keep sending error responses until the
        // app sends a termination request. Then close the session normally.

        // Continue sending pending response to adhere to valid locked-in principle.
        if (pending_digest_rsp_q) begin
          app_push_digest = 1'b1;
        end else begin
          // Now continuously send error responses until termination request arrives.
          app_error_rsp_valid = 1'b1;
          if (app_req.req_valid && app_req.req_last) begin
            app_req_ready = 1'b1;
            st_d          = StAppFinish;
          end
        end
      end

      StTerminalError: begin
        // this state is terminal
        st_d = st;
        sparse_fsm_error_o = 1'b 1;
        fsm_err.valid = 1'b 1;
        fsm_err.code = ErrFatalError;
        fsm_err.info = 24'(app_id);
      end

      default: begin
        st_d = StTerminalError;
        sparse_fsm_error_o = 1'b 1;
      end
    endcase

    // Error out if the key is used but it is invalid. Do not transition if:
    // - A request is outstanding (valid request but no handshake in this cycle). Otherwise a valid
    //   could be dropped which could bring the hashing engine in a non recoverable state.
    // - When the key error handling starts. Otherwise the FSM would get trapped.
    // Note, the key error is cleared when the error handling starts.
    if (err_key_used_but_invalid && !any_request_outstanding && st != StErrorKeyNotValid) begin
      st_d = StErrorKeyNotValid;
      // Track if error occurred during SW.
      err_during_sw_set = st == StSw;
    end

    // Track whether a hashing engine error occurred.
    err_sha3_during_app_set =
        error_i &&
        (st inside {StAppCfg, StAppMsg, StAppOutLen, StAppProcess, StAppWait, StAppPushDigest});

    // Enforce the entropy_fast_process bit is set to 0 for the duration of the error handling.
    // This ensures the hashing updates the PRNG and hence the masking is fully enabled. This
    // in turn ensures that no improperly masked hashing operation can be triggered by an
    // adversary.
    disable_entropy_fast_process =
        st inside {StErrorKeyNotValid, StErrorAwaitMsg, StErrorNotify, StErrorAwaitTermination,
                   StErrorFinish, StErrorAwaitSw, StErrorAwaitAbsorbed};

    // SEC_CM: FSM.GLOBAL_ESC, FSM.LOCAL_ESC
    // Unconditionally jump into the terminal error state if the life cycle controller triggers an
    // escalation.
    if (lc_ctrl_pkg::lc_tx_test_true_loose(lc_escalate_en_i)) begin
      st_d = StTerminalError;
    end
  end

  assign any_request_outstanding = app_req.req_valid && !app_rsp.req_ready;

  assign last_req_pending    = app_req.req_valid && app_req.req_last;
  // An empty message request issues a process command and does not forward any message data.
  assign process_cmd_pending = last_req_pending && app_req.strb == '0;
  assign last_req_hs         = last_req_pending && app_rsp.req_ready;

  // Track when last message part is handshaked. Note, this also tracks process commands.
  assign last_msg_part_received_d =
      clear_app_trackers         ? 1'b0 :                    // clear
      last_msg_part_received_set ? 1'b1 :                    // set
                                   last_msg_part_received_q; // hold

  assign process_cmd_sent_d =
      clear_app_trackers   ? 1'b0 :              // clear
      process_cmd_sent_set ? 1'b1 :              // set
                             process_cmd_sent_q; // hold

  // Track when SW acknowledges the error. Only set flag if this bit is relevant for the app
  // interface, i.e., a hashing operation is ongoing (this includes SW- and app-triggered
  // operations).
  assign err_processed_d =
      clear_app_trackers                  ? 1'b0 :           // clear
      (err_processed_i && (st != StIdle)) ? 1'b1 :           // set
                                            err_processed_q; // hold

  // Track errors occurring in SW mode.
  assign err_during_sw_d = clear_app_trackers ? 1'b0 : // clear
                           err_during_sw_set  ? 1'b1 : // set
                           err_during_sw_q;            // hold

  // Track hashing engine errors
  assign err_sha3_during_app_d = clear_app_trackers      ? 1'b0 : // clear
                                 err_sha3_during_app_set ? 1'b1 : // set
                                 err_sha3_during_app_q;           // hold

  // Track key invalid errors
  assign err_key_used_but_invalid_d = clear_app_trackers             ? 1'b0 : // clear
                                      err_key_used_but_invalid_clear ? 1'b0 : // clear when handled
                                      err_key_used_but_invalid_set   ? 1'b1 : // set
                                      err_key_used_but_invalid_q;             // hold

  // Factor out the clearing as it would affect the state transition logic but we want all
  // state dependent transition logic inside the FSM.
  assign err_key_used_but_invalid = err_key_used_but_invalid_set || err_key_used_but_invalid_q;

  // Track service rejected errors
  assign service_rejected_error_d = clear_app_trackers         ? 1'b0 :                    // clear
                                    service_rejected_error_set ? 1'b1 :                    // set
                                                                 service_rejected_error_q; // hold

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_msg_part_received_q   <= 1'b0;
      process_cmd_sent_q         <= 1'b0;
      pending_digest_rsp_q       <= 1'b0;
      pending_error_rsp_q        <= 1'b0;
      service_rejected_error_q   <= 1'b0;
      err_processed_q            <= 1'b0;
      err_during_sw_q            <= 1'b0;
      err_sha3_during_app_q      <= 1'b0;
      err_key_used_but_invalid_q <= 1'b0;
    end else begin
      last_msg_part_received_q   <= last_msg_part_received_d;
      process_cmd_sent_q         <= process_cmd_sent_d;
      pending_digest_rsp_q       <= pending_digest_rsp_d;
      pending_error_rsp_q        <= pending_error_rsp_d;
      service_rejected_error_q   <= service_rejected_error_d;
      err_processed_q            <= err_processed_d;
      err_during_sw_q            <= err_during_sw_d;
      err_sha3_during_app_q      <= err_sha3_during_app_d;
      err_key_used_but_invalid_q <= err_key_used_but_invalid_d;
    end
  end

  // Check that dynamic app only states are never entered for a static app.
  `ASSERT(InvalidStateForStaticApp_A,
          st inside {StErrorPush, StErrorAwaitTermination} |-> (app_cfg.if_type == AppDynamic),
          clk_i, rst_ni)

  //////////////
  // Datapath //
  //////////////

  // Encoded output length for the KMAC operation. The length is based upon the full app interface
  // response width.
  assign encoded_outlen      = EncodedOutLen[SelDigSize];
  assign encoded_outlen_strb = EncodedOutLenStrb[SelKeySize];

  // Data mux
  // This is the main datapath part of the app interface logic.
  // Once the FSM selected an interface and checked its configuration the message FIFO interface is
  // exposed to the interface. For a KMAC operation, as soon as the app has sent the last message
  // the FSM pushes the encoded output length into the message FIFO. This is a predefined value,
  // see `EncodeOutLen` parameter above.
  //
  // The data is forwarded depending on the masking parameters:
  // EnMasking = 1:
  // - For static and dynamic interface:
  //   - Masked = 0: Forward share 0. Set share 1 to '0.
  //   - Masked = 1: Forward both shares.
  // EnMasking = 0
  // - For static and dynamic interface:
  //   - Masked = 0: Forward share 0. Ignore share 1.
  //   - Masked = 1: Forward XOR of both shares.
  always_comb begin
    app_data_ready = 1'b 0;

    // Always accept a SW request even if SW is not active to avoid deadlocking the software. If
    // SW is not active, this request is ignored and will trigger an error (handled outside).
    sw_ready_o = 1'b 1;

    kmac_valid_o = 1'b 0;
    kmac_data_o  = '{default: '0};
    kmac_strb_o  = '0;

    unique case (mux_sel_buf_kmac)
      SelApp: begin
        // Forward message only if it contains data. An empty message / process command is not
        // forwarded.
        kmac_valid_o = app_req.req_valid && !process_cmd_pending;
        if (EnMasking) begin
          kmac_data_o[0] = app_req.data_s0;
          kmac_data_o[1] = app_cfg.masked ? app_req.data_s1 : '0;
        end else begin
          // If the interface is masked but the KMAC core not, then we unmask the input data.
          kmac_data_o[0] = app_cfg.masked ? app_req.data_s0 ^ app_req.data_s1 : app_req.data_s0;
        end
        // Expand byte strobe to bits for the prim_packer inside MSG_FIFO.
        for (int i = 0; i < MsgStrbW; i++) begin
          kmac_strb_o[8 * i +: 8] = {8{app_req.strb[i]}};
        end
        app_data_ready = kmac_ready_i;
      end

      SelOutLen: begin
        // Write encoded output length value as unmasked data (share 1 = '0).
        kmac_valid_o   = 1'b1; // always write
        kmac_data_o[0] = MsgWidth'(encoded_outlen);
        kmac_strb_o    = MsgWidth'(encoded_outlen_strb);
      end

      SelSw: begin
        // SW supports only one share
        kmac_valid_o   = sw_valid_i;
        kmac_data_o[0] = sw_data_i;
        for (int i = 1; i < Share; i++) begin
          kmac_data_o[i] = '0;
        end
        kmac_strb_o = sw_strb_i;
        sw_ready_o  = kmac_ready_i;
      end

      default: begin // Incl. SelNone
        kmac_valid_o = 1'b 0;
        kmac_data_o  = '{default: '0};
        kmac_strb_o  = '0;
      end

    endcase
  end

  // Error checking for Mux
  always_comb begin
    mux_err = '{valid: 1'b 0, code: ErrNone, info: '0};

    if (mux_sel_buf_err_check != SelSw && sw_valid_i) begin
      // If SW writes message into FIFO
      mux_err = '{
        valid: 1'b 1,
        code: ErrSwPushedMsgFifo,
        info: 24'({8'h 00, 8'(st), 8'(mux_sel_buf_err_check)})
      };
    end else if (app_active_o && sw_cmd_i != CmdNone) begin
      // If SW issues command except start
      mux_err = '{
        valid: 1'b 1,
        code: ErrSwIssuedCmdInAppActive,
        info: 24'(sw_cmd_i)
      };
    end
  end

  logic [AppMuxWidth-1:0] mux_sel_buf_output_logic;
  assign mux_sel_buf_output = app_mux_sel_e'(mux_sel_buf_output_logic);

  // SEC_CM: LOGIC.INTEGRITY
  prim_sec_anchor_buf #(
   .Width(AppMuxWidth)
  ) u_prim_buf_state_output_sel (
    .in_i(mux_sel),
    .out_o(mux_sel_buf_output_logic)
  );

  logic [AppMuxWidth-1:0] mux_sel_buf_err_check_logic;
  assign mux_sel_buf_err_check = app_mux_sel_e'(mux_sel_buf_err_check_logic);

  // SEC_CM: LOGIC.INTEGRITY
  prim_sec_anchor_buf #(
   .Width(AppMuxWidth)
  ) u_prim_buf_state_err_check (
    .in_i(mux_sel),
    .out_o(mux_sel_buf_err_check_logic)
  );

  logic [AppMuxWidth-1:0] mux_sel_buf_kmac_logic;
  assign mux_sel_buf_kmac = app_mux_sel_e'(mux_sel_buf_kmac_logic);

  // SEC_CM: LOGIC.INTEGRITY
  prim_sec_anchor_buf #(
   .Width(AppMuxWidth)
  ) u_prim_buf_state_kmac_sel (
    .in_i(mux_sel),
    .out_o(mux_sel_buf_kmac_logic)
  );

  // SEC_CM: LOGIC.INTEGRITY
  logic reg_state_valid;
  prim_sec_anchor_buf #(
   .Width(1)
  ) u_prim_buf_state_output_valid (
    .in_i(reg_state_valid),
    .out_o(reg_state_valid_o)
  );

  // Keccak state Demux
  // The state is only exposed to the registers if SW is active.
  always_comb begin
    reg_state_valid = 1'b0;
    reg_state_o     = '{default: '0};

    if ((mux_sel_buf_output == SelSw) &&
         lc_ctrl_pkg::lc_tx_test_false_strict(lc_escalate_en_i)) begin
      reg_state_valid = keccak_state_valid_i;
      reg_state_o     = keccak_state_i;
      // If key is sideloaded and KMAC is SW initiated hide the capacity from SW by zeroing.
      // See https://github.com/lowRISC/opentitan/issues/17508.
      if (keymgr_key_en_i) begin
        for (int i = 0; i < Share; i++) begin
          unique case (keccak_strength_q)
            L128: reg_state_o[i][sha3_pkg::StateW-1-:KeccakBitCapacity[L128]] = '0;
            L224: reg_state_o[i][sha3_pkg::StateW-1-:KeccakBitCapacity[L224]] = '0;
            L256: reg_state_o[i][sha3_pkg::StateW-1-:KeccakBitCapacity[L256]] = '0;
            L384: reg_state_o[i][sha3_pkg::StateW-1-:KeccakBitCapacity[L384]] = '0;
            L512: reg_state_o[i][sha3_pkg::StateW-1-:KeccakBitCapacity[L512]] = '0;
            default: reg_state_o[i] = '0;
          endcase
        end
      end
    end
  end

  ///////////////////
  // Digest pusher //
  ///////////////////
  // The maximal number of digest chunks is defined by the operation with the largest rate. The
  // bit-width of the rate for any XOF algorithm can be computed with: StateW - 2 * Strength.
  // And as SHA3, SHAKE, cSHAKE and KMAC have always a state width of 1600, the largest rate has
  // SHAKE-128 / cSHAKE-128 / KMAC-128 (the lowest strength).
  localparam int MaxNumDigestParts = (sha3_pkg::StateW - 2 * 128) / DynAppDigestW;
  localparam int DigestCntW        = $clog2(MaxNumDigestParts);
  logic [DigestCntW-1:0] digest_top;
  logic [DigestCntW-1:0] current_digest_idx;

  // Expose only the relevant part of the digest depending on the mode and strength. In case an
  // invalid mode or strength is detected, we set the digest_top to the smallest value.
  always_comb begin
    unique case (sha3_mode_q)
      sha3_pkg::Sha3: begin
        unique case (keccak_strength_q)
          sha3_pkg::L128: digest_top = DigestCntW'(128 / DynAppDigestW);
          // 224 is not a multiple of 64. Round up the number of digest parts. Note, due to this
          // rounding the interface exposes bits from the rate which are not part of the hash.
          sha3_pkg::L224: digest_top = DigestCntW'(4);
          sha3_pkg::L256: digest_top = DigestCntW'(256 / DynAppDigestW);
          sha3_pkg::L384: digest_top = DigestCntW'(384 / DynAppDigestW);
          sha3_pkg::L512: digest_top = DigestCntW'(512 / DynAppDigestW);
          default:        digest_top = DigestCntW'(128 / DynAppDigestW);
        endcase
      end
      sha3_pkg::Shake,
      sha3_pkg::CShake: begin
        // Expose the full rate for SHAKE, cSHAKE and KMAC. It is save to expose the full rate of
        // KMAC even if it exceeds the encoded output length.
        unique case (keccak_strength_q)
          sha3_pkg::L128: digest_top = DigestCntW'((sha3_pkg::StateW - 2 * 128) / DynAppDigestW);
          sha3_pkg::L224: digest_top = DigestCntW'((sha3_pkg::StateW - 2 * 224) / DynAppDigestW);
          sha3_pkg::L256: digest_top = DigestCntW'((sha3_pkg::StateW - 2 * 256) / DynAppDigestW);
          sha3_pkg::L384: digest_top = DigestCntW'((sha3_pkg::StateW - 2 * 384) / DynAppDigestW);
          sha3_pkg::L512: digest_top = DigestCntW'((sha3_pkg::StateW - 2 * 512) / DynAppDigestW);
          default:        digest_top = DigestCntW'((sha3_pkg::StateW - 2 * 512) / DynAppDigestW);
        endcase
      end
      default: digest_top = DigestCntW'(128 / DynAppDigestW);
    endcase
  end

  // Limit the response width to 64 bits because its the GCD for all modes except SHA-224.
  `ASSERT_INIT(DynAppDigestWIs64Bit_A, DynAppDigestW == 64)
  // Ensure all counter top computations divide properly as the response channel does not carry any
  // valid-strobe information.
  `ASSERT_INIT(DigestTopDividesSha3L128_A, 128 % DynAppDigestW == 0)
  // An exception is SHA3-224, where we fix the number of digest parts to 4, so the full hash and
  // some additional rate bits are sent.
  `ASSERT_INIT(DigestTopDividesSha3L256_A, 256 % DynAppDigestW == 0)
  `ASSERT_INIT(DigestTopDividesSha3L384_A, 384 % DynAppDigestW == 0)
  `ASSERT_INIT(DigestTopDividesSha3L512_A, 512 % DynAppDigestW == 0)

  `ASSERT_INIT(DigestTopDividesKmacAppDigestW_A, AppDigestW % DynAppDigestW == 0)

  `ASSERT_INIT(DigestTopDividesShakeL128_A, (sha3_pkg::StateW - 2 * 128) % DynAppDigestW == 0)
  `ASSERT_INIT(DigestTopDividesShakeL224_A, (sha3_pkg::StateW - 2 * 224) % DynAppDigestW == 0)
  `ASSERT_INIT(DigestTopDividesShakeL256_A, (sha3_pkg::StateW - 2 * 256) % DynAppDigestW == 0)
  `ASSERT_INIT(DigestTopDividesShakeL384_A, (sha3_pkg::StateW - 2 * 384) % DynAppDigestW == 0)
  `ASSERT_INIT(DigestTopDividesShakeL512_A, (sha3_pkg::StateW - 2 * 512) % DynAppDigestW == 0)

  assign digest_parts_available = current_digest_idx < digest_top;

  // Send parts of the digest if we are pushing.
  // Gate with digest_parts_available to prevent sending capacity-region bits when
  // current_digest_idx has already reached digest_top (the rate boundary).
  assign app_digest_valid = app_push_digest && digest_parts_available &&
                            lc_ctrl_pkg::lc_tx_test_false_strict(lc_escalate_en_i);

  // Only allow a squeeze if the app allows it.
  logic squeeze_again_allowed;
  assign squeeze_again_allowed = app_cfg.if_type == AppDynamic && app_cfg.session_cfg.en_xof;

  // Request a squeeze once we are out of digest parts.
  assign squeeze_again = squeeze_again_allowed && !digest_parts_available;

  logic digest_part_pushed;
  assign digest_part_pushed = app_digest_valid && app_req.rsp_ready;

  // Register if there is a digest response pending. If one is pending, any following response
  // (finish or error) must wait as otherwise data is changed which would violate the valid
  // locked-in principle.
  assign pending_digest_rsp_d = app_digest_valid && !digest_part_pushed;

  // Similarly, register if there is a pending error response.
  logic error_rsp_pushed;
  assign error_rsp_pushed    = app_error_rsp_valid && app_req.rsp_ready;
  assign pending_error_rsp_d = app_error_rsp_valid && !error_rsp_pushed;

  logic [DynAppDigestW-1:0] digest_part[Share];
  for (genvar i = 0; i < Share; i++) begin : g_digest_mux
    assign digest_part[i] = keccak_state_i[i][DynAppDigestW * current_digest_idx +: DynAppDigestW];
  end

  always_comb begin
    app_digest = '{default:'0};
    if (app_digest_valid) begin
      // Digest has always 2 entries. If !EnMasking, second is tied to 0.
      for (int i = 0 ; i < Share ; i++) begin
        // Return the portion of state.
        if (app_cfg.if_type == AppStatic) begin
          app_digest[i] = keccak_state_i[i][AppDigestW-1:0];
        end else if (app_cfg.if_type == AppDynamic) begin
          // Only expose a sub part. For SHA3-224, we set the capacity bits of the last response to
          // '0. See digest_top calculation above.
          app_digest[i][DynAppDigestW-1:0] = digest_part[i];
          if (sha3_mode_q == sha3_pkg::Sha3 && keccak_strength_q == sha3_pkg::L224 &&
              current_digest_idx == digest_top - 1) begin
            app_digest[i][DynAppDigestW-1:DynAppDigestW/2] = '0;
          end
        end
      end
    end
  end

  // SEC_CM CTR.REDUN
  prim_count #(
    .Width(DigestCntW),
    .PossibleActions(prim_count_pkg::Clr | prim_count_pkg::Incr)
  ) u_digest_part_counter (
    .clk_i,
    .rst_ni,
    .clr_i             (clear_digest_pusher),
    .set_i             (1'b0),
    .set_cnt_i         ('0),
    .incr_en_i         (1'b1),
    .decr_en_i         (1'b0),
    .step_i            (DigestCntW'(1)),
    .commit_i          (digest_part_pushed || clear_digest_pusher),
    .cnt_o             (current_digest_idx),
    .cnt_after_commit_o(),
    .err_o             (counter_error_o)
  );

  //////////////////
  // Key handling //
  //////////////////

  // Secret Key Mux
  // Prepare merged key if EnMasking is not set.
  // Combine share keys into unpacked array for logic below to assign easily.
  // SEC_CM: KEY.SIDELOAD
  logic [MaxKeyLen-1:0] keymgr_key[Share];
  if (EnMasking == 1) begin : g_masked_key
    for (genvar i = 0; i < Share; i++) begin : gen_key_pad
      assign keymgr_key[i] =  {(MaxKeyLen-KeyMgrKeyW)'(0), keymgr_key_i.key[i]};
    end
  end else begin : g_unmasked_key
    always_comb begin
      keymgr_key[0] = '0;
      for (int i = 0; i < keymgr_pkg::Shares; i++) begin
        keymgr_key[0][KeyMgrKeyW-1:0] ^= keymgr_key_i.key[i];
      end
    end
  end

  // Sideloaded key expose control
  assign err_key_used_but_invalid_set = keymgr_key_used && !keymgr_key_i.valid;

  always_comb begin
    keymgr_key_used = 1'b0;
    key_len_o = reg_key_len_i;
    for (int i = 0; i < Share; i++) begin
      key_data_o[i] = reg_key_data_i[i];
    end
    // The key is considered invalid in all cases that are not listed below (which includes idle and
    // error states).
    key_valid_o = 1'b0;

    unique case (st)
      StAppMsg, StAppOutLen, StAppProcess, StAppWait: begin
        // The key from KeyMgr is used if the current HW app interface does *keyed* MAC. This
        // module does not know the precise timing related to when the kmac_core module uses the
        // key during processing. To be on the safe side, we check that the key remains valid
        // directly after latching the configuration and throughout the entire processing until the
        // digest is received. The key is used by the kmac_core also after the kmac_app finished
        // sending the message. So we must check the key until we receive the digest because we
        // don't know here when the hashing engine starts the processing.
        keymgr_key_used = app_cfg.session_cfg.mode == AppKMAC;
        key_len_o       = SideloadedKey;
        for (int i = 0; i < Share; i++) begin
          key_data_o[i] = keymgr_key[i];
        end
        // Key is valid if the current HW app interface does *keyed* MAC and the key provided by
        // KeyMgr is valid.
        key_valid_o = keymgr_key_used && keymgr_key_i.valid;
      end

      StSw: begin
        if (keymgr_key_en_i) begin
          // Key from KeyMgr is actually used if *keyed* MAC is enabled.
          keymgr_key_used = kmac_en_q;
          key_len_o       = SideloadedKey;
          for (int i = 0; i < Share; i++) begin
            key_data_o[i] = keymgr_key[i];
          end
        end
        // Key is valid if SW does *keyed* MAC and ...
        if (kmac_en_q) begin
          if (!keymgr_key_en_i) begin
            // ... it uses the key from kmac's CSR, or ...
            key_valid_o = 1'b1;
          end else begin
            // ... it uses the key provided by KeyMgr and that one is valid.
            key_valid_o = keymgr_key_i.valid;
          end
        end
      end

      default: ;
    endcase
  end

  // Prefix Demux
  // For SW, always take the prefix from the register. For apps chose depending on configuration.
  always_comb begin
    sha3_prefix_o = '0;

    unique case (st)
      StAppCfg, StAppMsg, StAppOutLen, StAppProcess, StAppWait, StAppPushDigest: begin
        if (app_cfg.session_cfg.prefix_mode == 1'b0) begin
          sha3_prefix_o = reg_prefix_i;
        end else begin
          sha3_prefix_o = app_cfg.prefix;
        end
      end

      StSw: begin
        sha3_prefix_o = reg_prefix_i;
      end

      default: begin
        sha3_prefix_o = reg_prefix_i;
      end
    endcase
  end

  // Status - exclude error states so SW still can write messages during error recovery.
  assign app_active_o = (st inside {StAppCfg, StAppMsg, StAppOutLen, StAppProcess, StAppWait,
                                    StAppPushDigest, StAppFinish});

  // Error Reporting ==========================================================
  always_comb begin
    priority casez ({fsm_err.valid, mux_err.valid})
      2'b ?1: error_o = mux_err;
      2'b 10: error_o = fsm_err;
      default: error_o = '{valid: 1'b0, code: ErrNone, info: '0};
    endcase
  end

  ////////////////
  // Assertions //
  ////////////////

  // KeyMgr sideload key and the digest should be in the Key Length value
  `ASSERT_INIT(SideloadKeySameToDigest_A, KeyMgrKeyW <= AppDigestW)
  `ASSERT_INIT(AppIntfInRange_A, AppDigestW inside {128, 192, 256, 384, 512})

  // Issue(#13655): Having a coverage that sideload keylen and CSR keylen are
  // different.
  `COVER(AppIntfUseDifferentSizeKey_C,
    (st == StAppCfg && kmac_en_q) |-> reg_key_len_i != SideloadedKey)

endmodule
