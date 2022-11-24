// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Application interface

`include "prim_assert.sv"

module kmac_app
  import kmac_pkg::*;
#(
  // App specific configs are defined in kmac_pkg
  parameter  bit EnMasking = 1'b0,
  localparam int Share = (EnMasking) ? 2 : 1, // derived parameter
  parameter  bit SecIdleAcceptSwMsg = 1'b0
) (
  input clk_i,
  input rst_ni,

  // Secret Key from register
  input [MaxKeyLen-1:0] reg_key_data_i [Share],
  input key_len_e       reg_key_len_i,

  // Prefix from register
  input [sha3_pkg::NSRegisterSize*8-1:0] reg_prefix_i,

  // mode, strength, kmac_en from register
  input                             reg_kmac_en_i,
  input sha3_pkg::sha3_mode_e       reg_sha3_mode_i,
  input sha3_pkg::keccak_strength_e reg_keccak_strength_i,

  // Data from Software
  input                sw_valid_i,
  input [MsgWidth-1:0] sw_data_i,
  input [MsgWidth-1:0] sw_mask_i,
  output logic         sw_ready_o,

  // KeyMgr Sideload Key interface
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // Application Message in/ Digest out interface + control signals
  input  app_req_t [NumAppIntf-1:0] app_i,
  output app_rsp_t [NumAppIntf-1:0] app_o,

  // to KMAC Core: Secret key
  output logic [MaxKeyLen-1:0] key_data_o [Share],
  output key_len_e             key_len_o,

  // to MSG_FIFO
  output logic                kmac_valid_o,
  output logic [MsgWidth-1:0] kmac_data_o,
  output logic [MsgWidth-1:0] kmac_mask_o,
  input                       kmac_ready_i,

  // KMAC Core
  output logic kmac_en_o,

  // To Sha3 Core
  output logic [sha3_pkg::NSRegisterSize*8-1:0] sha3_prefix_o,
  output sha3_pkg::sha3_mode_e                  sha3_mode_o,
  output sha3_pkg::keccak_strength_e            keccak_strength_o,

  // STATE from SHA3 Core
  input                        keccak_state_valid_i,
  input [sha3_pkg::StateW-1:0] keccak_state_i [Share],

  // to STATE TL-window if Application is not active, the incoming state goes to
  // register if kdf_en is set, the state value goes to application and the
  // output to the register is all zero.
  output logic                        reg_state_valid_o,
  output logic [sha3_pkg::StateW-1:0] reg_state_o [Share],

  // Configurations If key_en is set, the logic uses KeyMgr's sideloaded key as
  // a secret key rather than register values. This only affects when software
  // initiates. If App initiates the hash operation and uses KMAC algorithm, it
  // always uses sideloaded key.
  input keymgr_key_en_i,

  // Commands
  // Command from software
  input kmac_cmd_e sw_cmd_i,

  // from SHA3
  input prim_mubi_pkg::mubi4_t absorbed_i,

  // to KMAC
  output kmac_cmd_e cmd_o,

  // to SW
  output prim_mubi_pkg::mubi4_t absorbed_o,

  // To status
  output logic app_active_o,

  // Status
  // - entropy_ready_i: Entropy configured by SW. It is used to check if App
  //                    is OK to request.
  input prim_mubi_pkg::mubi4_t entropy_ready_i,

  // Error input
  // This error comes from KMAC/SHA3 engine.
  // KeyMgr interface delivers the error signal to KeyMgr to drop the current op
  // and re-initiate.
  // If error happens, regardless of SW-initiated or KeyMgr-initiated, the error
  // is reported to the ERR_CODE so that SW can look into.
  input error_i,

  // SW sets err_processed bit in CTRL then the logic goes to Idle
  input err_processed_i,

  // error_o value is pushed to Error FIFO at KMAC/SHA3 top and reported to SW
  output kmac_pkg::err_t error_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  output logic sparse_fsm_error_o
);

  /////////////////
  // Definitions //
  /////////////////

  // Digest width is same to the key width `keymgr_pkg::KeyWidth`.
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

  localparam logic [OutLenW-1:0] EncodedOutLenMask [5] = '{
    24'h 00FFFF, // Key128,
    24'h 00FFFF, // Key192
    24'h FFFFFF, // Key256
    24'h FFFFFF, // Key384
    24'h FFFFFF  // Key512
  };

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 11 -n 10 \
  //      -s 155490773 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: ||||||||||||| (14.55%)
  //  4: |||||||||||||||||||| (21.82%)
  //  5: |||||||||||||||||| (20.00%)
  //  6: |||||||||||||||||||| (21.82%)
  //  7: |||||||||||||||||| (20.00%)
  //  8: | (1.82%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 9
  //
  localparam int StateWidth = 10;
  // States
  //  StIdle                  = 10'b0101110011,
  //  StAppCfg                = 10'b0001010000,
  //  StAppMsg                = 10'b0001011111,
  //  StAppOutLen             = 10'b1011001111,
  //  StAppProcess            = 10'b1000100110,
  //  StAppWait               = 10'b0010010110,
  //  StSw                    = 10'b0111111111,
  //  StKeyMgrErrKeyNotValid  = 10'b1001110100,
  //  StError                 = 10'b1101011101,
  //  StServiceRejectedError  = 10'b1110000110,
  //  StTerminalError         = 10'b0010001001
  typedef enum logic [StateWidth-1:0] {
    StIdle = 10'b0101110011,

    // Application operation.
    //
    // if start request comes from an App first, until the operation ends by the
    // requested App, all operations are granted to the specific App. SW
    // requests and other Apps requests will be ignored.
    //
    // App interface does not have control signals. When first data valid occurs
    // from an App, this logic asserts the start command to the downstream. When
    // last beat pulse comes, this logic asserts the process to downstream
    // (after the transaction is accepted regardless of partial writes or not)
    // When absorbed by SHA3 core, the logic sends digest to the requested App
    // and right next cycle, it triggers done command to downstream.

    // In StAppCfg state, it latches the cfg from AppCfg parameter to determine
    // the kmac_mode, sha3_mode, keccak strength.
    StAppCfg = 10'b0001010000,

    StAppMsg = 10'b0001011111,

    // In StKeyOutLen, this module pushes encoded outlen to the MSG_FIFO.
    // Assume the length is 256 bit, the data will be 48'h 02_0100
    StAppOutLen  = 10'b1011001111,
    StAppProcess = 10'b1000100110,
    StAppWait    = 10'b0010010110,

    // SW Controlled
    // If start request comes from SW first, until the operation ends, all
    // requests from KeyMgr will be discarded.
    StSw = 10'b0111111111,

    // Error KeyNotValid
    // When KeyMgr operates, the secret key is not ready yet.
    StKeyMgrErrKeyNotValid = 10'b1001110100,

    StError = 10'b1101011101,

    StServiceRejectedError = 10'b1110000110,

    // This state is used for terminal errors
    StTerminalError = 10'b0010001001
  } st_e;

  /////////////
  // Signals //
  /////////////

  st_e st, st_d;

  // app_rsp_t signals
  // The state machine controls mux selection, which controls the ready signal
  // the other responses are controled in separate logic. So define the signals
  // here and merge them to the response.
  logic app_data_ready, fsm_data_ready;
  logic app_digest_done, fsm_digest_done_q, fsm_digest_done_d;
  logic [AppDigestW-1:0] app_digest [2];

  // One more slot for value NumAppIntf. It is the value when no app intf is
  // chosen.
  localparam int unsigned AppIdxW = $clog2(NumAppIntf);

  // app_id indicates, which app interface was chosen. various logic use this
  // value to get the config or return the data.
  logic [AppIdxW-1:0] app_id, app_id_d;
  logic               clr_appid, set_appid;

  // Output length
  logic [OutLenW-1:0] encoded_outlen, encoded_outlen_mask;

  // state output
  // Mux selection signal
  app_mux_sel_e mux_sel;
  app_mux_sel_e mux_sel_buf_output;
  app_mux_sel_e mux_sel_buf_err_check;
  app_mux_sel_e mux_sel_buf_kmac;

  // Error checking logic

  kmac_pkg::err_t fsm_err, mux_err;

  logic service_rejected_error;
  logic service_rejected_error_set, service_rejected_error_clr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                         service_rejected_error <= 1'b 0;
    else if (service_rejected_error_set) service_rejected_error <= 1'b 1;
    else if (service_rejected_error_clr) service_rejected_error <= 1'b 0;
  end

  ////////////////////////////
  // Application Mux/ Demux //
  ////////////////////////////


  // Processing return data.
  // sends to only selected app intf.
  // clear digest right after done to not leak info to other interface
  always_comb begin
    for (int unsigned i = 0 ; i < NumAppIntf ; i++) begin
      if (i == app_id) begin
        app_o[i] = '{
          ready:         app_data_ready | fsm_data_ready,
          done:          app_digest_done | fsm_digest_done_q,
          digest_share0: app_digest[0],
          digest_share1: app_digest[1],
          // if fsm asserts done, should be an error case.
          error:         error_i | fsm_digest_done_q | sparse_fsm_error_o
                         | service_rejected_error
        };
      end else begin
        app_o[i] = '{
          ready: 1'b 0,
          done:  1'b 0,
          digest_share0: '0,
          digest_share1: '0,
          error: 1'b 0
        };
      end
    end // for {i, NumAppIntf, i++}
  end // aiways_comb

  // app_id latch
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) app_id <= AppIdxW'(0) ; // Do not select any
    else if (clr_appid) app_id <= AppIdxW'(0);
    else if (set_appid) app_id <= app_id_d;
  end

  // app_id selection as of now, app_id uses Priority. The assumption is that
  //  the request normally does not collide. (ROM_CTRL activates very early
  //  stage at the boot sequence)
  //
  //  If this assumption is not true, consider RR arbiter.

  // Prep for arbiter
  logic [NumAppIntf-1:0] app_reqs;
  logic [NumAppIntf-1:0] unused_app_gnts;
  logic [$clog2(NumAppIntf)-1:0] arb_idx;
  logic arb_valid;
  logic arb_ready;

  always_comb begin
    app_reqs = '0;
    for (int unsigned i = 0 ; i < NumAppIntf ; i++) begin
      app_reqs[i] = app_i[i].valid;
    end
  end

  prim_arbiter_fixed #(
    .N (NumAppIntf),
    .DW(1),
    .EnDataPort(1'b 0)
  ) u_appid_arb (
    .clk_i,
    .rst_ni,

    .req_i  (app_reqs),
    .data_i ('{default:'0}),
    .gnt_o  (unused_app_gnts),
    .idx_o  (arb_idx),

    .valid_o (arb_valid),
    .data_o  (), // not used
    .ready_i (arb_ready)
  );

  assign app_id_d = AppIdxW'(arb_idx);
  assign arb_ready = set_appid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) fsm_digest_done_q <= 1'b 0;
    else         fsm_digest_done_q <= fsm_digest_done_d;
  end

  /////////
  // FSM //
  /////////

  // State register
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, st_d, st, st_e, StIdle)

  // Create a lint error to reduce the risk of accidentally enabling this feature.
  `ASSERT_STATIC_LINT_ERROR(KmacSecIdleAcceptSwMsgNonDefault, SecIdleAcceptSwMsg == 0)

  // Next State & output logic
  // SEC_CM: FSM.SPARSE
  always_comb begin
    st_d = st;

    mux_sel = SecIdleAcceptSwMsg ? SelSw : SelNone;

    // app_id control
    set_appid = 1'b 0;
    clr_appid = 1'b 0;

    // Commands
    cmd_o = CmdNone;

    // Software output
    absorbed_o = prim_mubi_pkg::MuBi4False;

    // Error
    fsm_err = '{valid: 1'b 0, code: ErrNone, info: '0};
    sparse_fsm_error_o = 1'b 0;

    service_rejected_error_set = 1'b 0;
    service_rejected_error_clr = 1'b 0;

    // If error happens, FSM asserts data ready but discard incoming msg
    fsm_data_ready = 1'b 0;
    fsm_digest_done_d = 1'b 0;

    unique case (st)
      StIdle: begin
        if (arb_valid) begin
          st_d = StAppCfg;

          // choose app_id
          set_appid = 1'b 1;
        end else if (sw_cmd_i == CmdStart) begin
          st_d = StSw;
          // Software initiates the sequence
          cmd_o = CmdStart;
        end else begin
          st_d = StIdle;
        end
      end

      StAppCfg: begin
        if (AppCfg[app_id].Mode == AppKMAC &&
          prim_mubi_pkg::mubi4_test_false_strict(entropy_ready_i)) begin
          // Check if the entropy is not configured but it is needed in
          // `AppCfg[app_id]` (KMAC mode).
          //
          // SW is not properly configured, report and not request Hashing
          // Return the app with errors
          st_d = StError;

          service_rejected_error_set = 1'b 1;

        end else if ((AppCfg[app_id].Mode == AppKMAC) &&
          !keymgr_key_i.valid) begin
          st_d = StKeyMgrErrKeyNotValid;

          // As mux_sel is not set to SelApp, app_data_ready is still 0.
          // This logic won't accept the requests from the selected App.

        end else begin
          // As Cfg is stable now, it sends cmd
          st_d = StAppMsg;

          // App initiates the data
          cmd_o = CmdStart;
        end
      end

      StAppMsg: begin
        mux_sel = SelApp;
        if (app_i[app_id].valid && app_o[app_id].ready && app_i[app_id].last) begin
          if (AppCfg[app_id].Mode == AppKMAC) begin
            st_d = StAppOutLen;
          end else begin
            st_d = StAppProcess;
          end
        end else begin
          st_d = StAppMsg;
        end
      end

      StAppOutLen: begin
        mux_sel = SelOutLen;

        if (kmac_valid_o && kmac_ready_i) begin
          st_d = StAppProcess;
        end else begin
          st_d = StAppOutLen;
        end
      end

      StAppProcess: begin
        cmd_o = CmdProcess;
        st_d = StAppWait;
      end

      StAppWait: begin
        if (prim_mubi_pkg::mubi4_test_true_strict(absorbed_i)) begin
          // Send digest to KeyMgr and complete the op
          st_d = StIdle;
          cmd_o = CmdDone;

          clr_appid = 1'b 1;
        end else begin
          st_d = StAppWait;
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

      StKeyMgrErrKeyNotValid: begin
        st_d = StError;

        // As mux_sel is not set to SelApp, app_data_ready is still 0.
        // This logic won't accept the requests from the selected App.
        fsm_err.valid = 1'b 1;
        fsm_err.code = ErrKeyNotValid;
        fsm_err.info = 24'(app_id);
      end

      StError: begin
        // In this state, the state machine flush out the request
        st_d = StError;

        fsm_data_ready = 1'b 1;

        if (err_processed_i) begin
          st_d = StIdle;

          // clear internal variables
          clr_appid = 1'b 1;
        end

        if (app_i[app_id].valid && app_i[app_id].last) begin
          // Send garbage digest to the app interface to complete transaction
          fsm_digest_done_d = 1'b 1;

          if (service_rejected_error) begin
            // If service was rejected, it is assumed the SW is not loaded
            // yet. In this case, return the request with error and keep
            // moving, hoping SW may handle the errors later
            st_d = StServiceRejectedError;
          end
        end

      end

      StServiceRejectedError: begin
        // Clear the error and move to Idle
        // At this state, the app responses the request with an error.
        st_d = StIdle;

        clr_appid = 1'b 1;
        service_rejected_error_clr = 1'b 1;
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

    // SEC_CM: FSM.GLOBAL_ESC, FSM.LOCAL_ESC
    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      st_d = StTerminalError;
    end
  end

  //////////////
  // Datapath //
  //////////////

  // Encoded output length
  assign encoded_outlen      = EncodedOutLen[SelDigSize];
  assign encoded_outlen_mask = EncodedOutLenMask[SelKeySize];

  // Data mux
  // This is the main part of the KeyMgr interface logic.
  // The FSM selects KeyMgr interface in a cycle after it receives the first
  // valid data from KeyMgr. The ready signal to the KeyMgr data interface
  // represents the MSG_FIFO ready, only when it is in StKeyMgrMsg state.
  // After KeyMgr sends last beat, the kmac interface (to MSG_FIFO) is switched
  // to OutLen. OutLen is pre-defined values. See `EncodeOutLen` parameter above.
  always_comb begin
    app_data_ready = 1'b 0;
    sw_ready_o = 1'b 1;

    kmac_valid_o = 1'b 0;
    kmac_data_o = '0;
    kmac_mask_o = '0;

    unique case (mux_sel_buf_kmac)
      SelApp: begin
        // app_id is valid at this time
        kmac_valid_o = app_i[app_id].valid;
        kmac_data_o  = app_i[app_id].data;
        // Expand strb to bits. prim_packer inside MSG_FIFO accepts the bit masks
        for (int i = 0 ; i < $bits(app_i[app_id].strb) ; i++) begin
          kmac_mask_o[8*i+:8] = {8{app_i[app_id].strb[i]}};
        end
        app_data_ready = kmac_ready_i;
      end

      SelOutLen: begin
        // Write encoded output length value
        kmac_valid_o = 1'b 1; // always write
        kmac_data_o  = MsgWidth'(encoded_outlen);
        kmac_mask_o  = MsgWidth'(encoded_outlen_mask);
      end

      SelSw: begin
        kmac_valid_o = sw_valid_i;
        kmac_data_o  = sw_data_i ;
        kmac_mask_o  = sw_mask_i ;
        sw_ready_o   = kmac_ready_i ;
      end

      default: begin // Incl. SelNone
        kmac_valid_o = 1'b 0;
        kmac_data_o = '0;
        kmac_mask_o = '0;
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
  // Keccak state --> Register output is enabled when state is in StSw
  always_comb begin
    if ((mux_sel_buf_output == SelSw) && (lc_escalate_en_i == lc_ctrl_pkg::Off)) begin
      reg_state_valid = keccak_state_valid_i;
      reg_state_o = keccak_state_i;
    end else begin
      reg_state_valid = 1'b 0;
      reg_state_o = '{default:'0};
    end
  end

  // Keccak state --> KeyMgr
  always_comb begin
    app_digest_done = 1'b 0;
    app_digest = '{default:'0};
    if (st == StAppWait && prim_mubi_pkg::mubi4_test_true_strict(absorbed_i) &&
        lc_escalate_en_i == lc_ctrl_pkg::Off) begin
      // SHA3 engine has calculated the hash. Return the data to KeyMgr
      app_digest_done = 1'b 1;

      // digest has always 2 entries. If !EnMasking, second is tied to 0.
      for (int i = 0 ; i < Share ; i++) begin
        // Return the portion of state.
        app_digest[i] = keccak_state_i[i][AppDigestW-1:0];
      end
    end
  end


  // Secret Key Mux

  // Prepare merged key if EnMasking is not set.
  // Combine share keys into unpacked array for logic below to assign easily.
  // SEC_CM: KEY.SIDELOAD
  logic [MaxKeyLen-1:0] keymgr_key [Share];
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

  // Sideloaded key manage: Keep use sideloaded key for KMAC AppIntf until the
  // hashing operation is finished.
  always_comb begin
    key_len_o  = reg_key_len_i;
    for (int i = 0 ; i < Share; i++) begin
      key_data_o[i] = reg_key_data_i[i];
    end

    unique case (st)
      StAppCfg, StAppMsg, StAppOutLen, StAppProcess, StAppWait: begin
        key_len_o = SideloadedKey;
        for (int i = 0 ; i < Share; i++) begin
          key_data_o[i] = keymgr_key[i];
        end
      end

      StSw: begin
        if (keymgr_key_en_i) begin
          key_len_o = SideloadedKey;
          for (int i = 0 ; i < Share; i++) begin
            key_data_o[i] = keymgr_key[i];
          end
        end
      end

      default: ;
    endcase
  end

  // Prefix Demux
  // For SW, always prefix register.
  // For App intf, check PrefixMode cfg and if 1, use Prefix cfg.
  always_comb begin
    sha3_prefix_o = '0;

    unique case (st)
      StAppCfg, StAppMsg, StAppOutLen, StAppProcess, StAppWait: begin
        // Check app intf cfg
        for (int unsigned i = 0 ; i < NumAppIntf ; i++) begin
          if (app_id == i) begin
            if (AppCfg[i].PrefixMode == 1'b 0) begin
              sha3_prefix_o = reg_prefix_i;
            end else begin
              sha3_prefix_o = AppCfg[i].Prefix;
            end
          end
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

  // KMAC en / SHA3 mode / Strength
  //  by default, it uses reg cfg. When app intf reqs come, it uses AppCfg.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      kmac_en_o         <= 1'b 0;
      sha3_mode_o       <= sha3_pkg::Sha3;
      keccak_strength_o <= sha3_pkg::L256;
    end else if (clr_appid) begin
      // As App completed, latch reg value
      kmac_en_o         <= reg_kmac_en_i;
      sha3_mode_o       <= reg_sha3_mode_i;
      keccak_strength_o <= reg_keccak_strength_i;
    end else if (set_appid) begin
      kmac_en_o         <= AppCfg[arb_idx].Mode == AppKMAC ? 1'b 1 : 1'b 0;
      sha3_mode_o       <= AppCfg[arb_idx].Mode == AppSHA3
                           ? sha3_pkg::Sha3 : sha3_pkg::CShake;
      keccak_strength_o <= AppCfg[arb_idx].Strength ;
    end else if (st == StIdle) begin
      kmac_en_o         <= reg_kmac_en_i;
      sha3_mode_o       <= reg_sha3_mode_i;
      keccak_strength_o <= reg_keccak_strength_i;
    end
  end

  // Status
  assign app_active_o = (st inside {StAppCfg, StAppMsg, StAppOutLen,
                                    StAppProcess, StAppWait});

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
    (st == StAppCfg && kmac_en_o) |-> reg_key_len_i != SideloadedKey)

endmodule
