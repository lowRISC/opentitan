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
  localparam int Share = (EnMasking) ? 2 : 1 // derived parameter
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
  output [MaxKeyLen-1:0] key_data_o [Share],
  output key_len_e       key_len_o,

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
  input absorbed_i,

  // to KMAC
  output kmac_cmd_e cmd_o,

  // to SW
  output logic absorbed_o,

  // Error input
  // This error comes from KMAC/SHA3 engine.
  // KeyMgr interface delivers the error signal to KeyMgr to drop the current op
  // and re-initiate.
  // If error happens, regardless of SW-initiated or KeyMgr-initiated, the error
  // is reported to the ERR_CODE so that SW can look into.
  input error_i,

  // error_o value is pushed to Error FIFO at KMAC/SHA3 top and reported to SW
  output kmac_pkg::err_t error_o
);

  /////////////////
  // Definitions //
  /////////////////

  // Digest width is same to the key width `keymgr_pkg::KeyWidth`.
  localparam int KeyMgrKeyW = $bits(keymgr_key_i.key_share0);

  localparam key_len_e KeyLen [5] = '{Key128, Key192, Key256, Key384, Key512};

  localparam int SelKeySize = (AppDigestW == 128) ? 0 :
                              (AppDigestW == 192) ? 1 :
                              (AppDigestW == 256) ? 2 :
                              (AppDigestW == 384) ? 3 :
                              (AppDigestW == 512) ? 4 : 0 ;
  localparam key_len_e SideloadedKey = KeyLen[SelKeySize];

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

  // States
  typedef enum logic [3:0] {
    StIdle = 4'b 0000,

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
    StAppCfg = 4'b 1110,

    StAppMsg = 4'b 0101,

    // In StKeyOutLen, this module pushes encoded outlen to the MSG_FIFO.
    // Assume the length is 256 bit, the data will be 48'h 02_0100
    StAppOutLen = 4'b 0110,
    StAppProcess = 4'b 1010,
    StAppWait = 4'b 0111,

    // SW Controlled
    // If start request comes from SW first, until the operation ends, all
    // requests from KeyMgr will be discarded.
    StSw = 4'b 0100,

    // Error KeyNotValid
    // When KeyMgr operates, the secret key is not ready yet.
    StKeyMgrErrKeyNotValid = 4'b 1111
  } keyctrl_st_e;

  typedef enum logic [2:0] {
    SelNone = 3'b 000,
    SelApp = 3'b 101,
    SelOutLen = 3'b 110,
    SelSw = 3'b 010
  } mux_sel_e ;

  /////////////
  // Signals //
  /////////////

  keyctrl_st_e st, st_d;

  // app_rsp_t signals
  // The state machine controls mux selection, which controls the ready signal
  // the other responses are controled in separate logic. So define the signals
  // here and merge them to the response.
  logic app_data_ready;
  logic app_digest_done;
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
  mux_sel_e mux_sel;

  // Error checking logic

  kmac_pkg::err_t fsm_err, mux_err;

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
          ready:         app_data_ready,
          done:          app_digest_done,
          digest_share0: app_digest[0],
          digest_share1: app_digest[1],
          error:         error_i
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

  /////////
  // FSM //
  /////////

  // State register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st <= StIdle;
    else         st <= st_d;
  end

  // Next State & output logic
  always_comb begin
    st_d = StIdle;

    mux_sel = SelNone;

    // app_id control
    set_appid = 1'b 0;
    clr_appid = 1'b 0;

    // Commands
    cmd_o = CmdNone;

    // Software output
    absorbed_o = 1'b 0;

    // Error
    fsm_err = '{valid: 1'b 0, code: ErrNone, info: '0};

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

        if ((AppCfg[app_id].Mode == AppKMAC) && !keymgr_key_i.valid) begin
          st_d = StKeyMgrErrKeyNotValid;

          fsm_err.valid = 1'b 1;
          fsm_err.code = ErrKeyNotValid;
          fsm_err.info = '0;
        end else begin
          // As Cfg is stable now, it sends cmd
          st_d = StAppMsg;

          // App initiates the data
          cmd_o = CmdStart;
        end
      end

      StAppMsg: begin
        mux_sel = SelApp;
        // Wait until the completion (done) from KeyMgr?
        // Or absorb completion?
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
        if (absorbed_i) begin
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
        st_d = StKeyMgrErrKeyNotValid;
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

  //////////////
  // Datapath //
  //////////////

  // Encoded output length
  assign encoded_outlen      = EncodedOutLen[SelKeySize];
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

    unique case (mux_sel)
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

    if (mux_sel != SelSw) begin
      if (sw_valid_i) begin
        // If SW writes message into FIFO
        mux_err = '{
          valid: 1'b 1,
          code: ErrSwPushedMsgFifo,
          info: 24'({8'h 00, 8'(st), 8'(mux_sel)})
        };
      end else if (!(sw_cmd_i inside {CmdNone, CmdStart})) begin
        // If SW issues command except start
        mux_err = '{
          valid: 1'b 1,
          code: ErrSwPushedWrongCmd,
          info: 24'(sw_cmd_i)
        };
      end
    end
  end

  // Keccak state Demux
  // Keccak state --> Register output is enabled when state is in StSw
  always_comb begin
    if (mux_sel == SelSw) begin
      reg_state_valid_o = keccak_state_valid_i;
      reg_state_o = keccak_state_i;
    end else begin
      reg_state_valid_o = 1'b 0;
      reg_state_o = '{default:'0};
    end
  end

  // Keccak state --> KeyMgr
  always_comb begin
    app_digest_done = 1'b 0;
    app_digest = '{default:'0};
    if (st == StAppWait && absorbed_i) begin
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
  logic [MaxKeyLen-1:0] keymgr_key [Share];
  if (EnMasking == 1) begin : g_masked_key
    assign keymgr_key[0] =  {(MaxKeyLen-KeyMgrKeyW)'(0), keymgr_key_i.key_share0};
    assign keymgr_key[1] =  {(MaxKeyLen-KeyMgrKeyW)'(0), keymgr_key_i.key_share1};
  end else begin : g_unmasked_key
    assign keymgr_key[0] = {(MaxKeyLen-KeyMgrKeyW)'(0),
                            keymgr_key_i.key_share0 ^ keymgr_key_i.key_share1};
  end

  // Sideloaded key is used when KeyMgr KDF is active or !!CFG.sideload is set
  always_comb begin
    if (keymgr_key_en_i || (mux_sel == SelApp)) begin
      // KeyLen is fixed to the $bits(sideloaded_key)
      key_len_o = SideloadedKey;
    end else begin
      key_len_o = reg_key_len_i;
    end
  end

  for (genvar i = 0 ; i < Share ; i++) begin : g_key_assign
    assign key_data_o[i] = (keymgr_key_en_i || (mux_sel == SelApp))
                         ? keymgr_key[i]
                         : reg_key_data_i[i] ;
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
  `ASSERT_INIT(SideloadKeySameToDigest_A, KeyMgrKeyW == AppDigestW)
  `ASSERT_INIT(AppIntfInRange_A, AppDigestW inside {128, 192, 256, 384, 512})


endmodule
