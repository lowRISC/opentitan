// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC/SHA3

`include "prim_assert.sv"

module kmac
  import kmac_pkg::*;
  import kmac_reg_pkg::*;
#(
  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter bit EnMasking = 1,

  // ReuseShare: If set, keccak_round logic only consumes small portion of
  // entropy, not 1600bit of entropy at every round. It uses adjacent shares
  // as entropy inside Domain-Oriented Masking AND logic.
  // This parameter only affects when `EnMasking` is set.
  parameter bit ReuseShare = 0,

  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,

  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,

  input clk_edn_i,
  input rst_edn_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // KeyMgr sideload (secret key) interface
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // KeyMgr KDF data path
  input  app_req_t [NumAppIntf-1:0] app_i,
  output app_rsp_t [NumAppIntf-1:0] app_o,

  // EDN interface
  output edn_pkg::edn_req_t entropy_o,
  input  edn_pkg::edn_rsp_t entropy_i,

  // interrupts
  output logic intr_kmac_done_o,
  output logic intr_fifo_empty_o,
  output logic intr_kmac_err_o,

  // parameter consistency check with keymgr
  output logic en_masking_o,

  // Idle signal
  output logic idle_o
);

  ////////////////
  // Parameters //
  ////////////////
  localparam int Share = (EnMasking) ? 2 : 1 ;

  /////////////////
  // Definitions //
  /////////////////
  // This state machine is to track the current process based on SW input and
  // KMAC operation.
  typedef enum logic [2:0] {
    // Idle state
    KmacIdle,

    // When software writes CmdStart @ KmacIdle and kmac_en, FSM moves to this
    KmacPrefix,

    // When SHA3 engine processes Key block, FSM moves to here.
    KmacKeyBlock,

    // Message Feed
    KmacMsgFeed,

    // Complete and squeeze
    KmacDigest

  } kmac_st_e;
  kmac_st_e kmac_st, kmac_st_d;

  /////////////
  // Signals //
  /////////////
  kmac_reg2hw_t reg2hw;
  kmac_hw2reg_t hw2reg;

  // devmode ties to 1 as KMAC should be operated at the beginning for ROM_CTRL.
  logic devmode;
  assign devmode = 1'b 1;

  // Window
  typedef enum int {
    WinState   = 0,
    WinMsgFifo = 1
  } tl_window_e;

  tlul_pkg::tl_h2d_t tl_win_h2d[2];
  tlul_pkg::tl_d2h_t tl_win_d2h[2];

  // SHA3 core control signals and its response.
  // Sequence: start --> process(multiple) --> get absorbed event --> {run -->} done
  logic sha3_start, sha3_run, sha3_done, sha3_absorbed, unused_sha3_squeeze;

  // Indicate one block processed
  logic sha3_block_processed;

  // EStatus for entropy
  logic entropy_in_keyblock;

  // KeyMgr interface logic generates event_absorbed from sha3_absorbed.
  // It is active only if SW initiates the hashing engine.
  logic event_absorbed;

  sha3_pkg::sha3_st_e sha3_fsm;

  // Prefix: kmac_pkg defines Prefix based on N size and S size.
  // Then computes left_encode(len(N)) size and left_encode(len(S))
  // For given default value 32, 256 bits, the max
  // encode_string(N) || encode_string(S) is 328. So 11 Prefix registers are
  // created.
  logic [sha3_pkg::NSRegisterSize*8-1:0] reg_ns_prefix;
  logic [sha3_pkg::NSRegisterSize*8-1:0] ns_prefix;

  // NumWordsPrefix from kmac_reg_pkg
  `ASSERT_INIT(PrefixRegSameToPrefixPkg_A,
               kmac_reg_pkg::NumWordsPrefix*4 == sha3_pkg::NSRegisterSize)

  // Output state: this is used to redirect the digest to KeyMgr or Software
  // depends on the configuration.
  logic state_valid;
  logic [sha3_pkg::StateW-1:0] state [Share];

  // state is de-muxed in keymgr interface logic.
  // the output from keymgr logic goes into staterd module to be visible to SW
  logic unused_reg_state_valid;
  logic [sha3_pkg::StateW-1:0] reg_state [Share];

  // SHA3 Entropy interface
  logic sha3_rand_valid, sha3_rand_consumed;
  logic [sha3_pkg::StateW-1:0] sha3_rand_data;

  // FIFO related signals
  logic msgfifo_empty, msgfifo_full;
  logic [kmac_pkg::MsgFifoDepthW-1:0] msgfifo_depth;

  logic                          msgfifo_valid       ;
  logic [kmac_pkg::MsgWidth-1:0] msgfifo_data [Share];
  logic [kmac_pkg::MsgStrbW-1:0] msgfifo_strb        ;
  logic                          msgfifo_ready       ;

  if (EnMasking) begin : gen_msgfifo_data_masked
    // In Masked mode, the input message data is split into two shares.
    // Only concern, however, here is the secret key. So message can be
    // put into only one share and other is 0.
    assign msgfifo_data[1] = '0;
  end

  // TL-UL Adapter(MSG_FIFO) signals
  logic        tlram_req;
  logic        tlram_gnt;
  logic        tlram_we;
  logic [8:0]  tlram_addr;   // NOT_READ
  logic [31:0] tlram_wdata;
  logic [31:0] tlram_wmask;
  logic [31:0] tlram_rdata;
  logic        tlram_rvalid;
  logic [1:0]  tlram_rerror;
  logic [31:0] tlram_wdata_endian;
  logic [31:0] tlram_wmask_endian;

  logic                          sw_msg_valid;
  logic [kmac_pkg::MsgWidth-1:0] sw_msg_data ;
  logic [kmac_pkg::MsgWidth-1:0] sw_msg_mask ;
  logic                          sw_msg_ready;

  // KeyMgr interface to MSG_FIFO
  logic                          mux2fifo_valid;
  logic [kmac_pkg::MsgWidth-1:0] mux2fifo_data ;
  logic [kmac_pkg::MsgWidth-1:0] mux2fifo_mask ;
  logic                          mux2fifo_ready;

  // KMAC to SHA3 core
  logic                          msg_valid       ;
  logic [kmac_pkg::MsgWidth-1:0] msg_data [Share];
  logic [kmac_pkg::MsgStrbW-1:0] msg_strb        ;
  logic                          msg_ready       ;

  // Process control signals
  // Process pulse propagates from register to SHA3 engine one by one.
  // Each module (MSG_FIFO, KMAC core, SHA3 core) generates the process pulse
  // after flushing internal data to the next module.
  logic reg2msgfifo_process, msgfifo2kmac_process, kmac2sha3_process;


  // Secret Key signals
  logic [MaxKeyLen-1:0] sw_key_data [Share];
  key_len_e             sw_key_len;
  logic [MaxKeyLen-1:0] key_data [Share];
  key_len_e             key_len;

  // SHA3 Mode, Strength, KMAC enable for app interface
  logic                       reg_kmac_en,         app_kmac_en;
  sha3_pkg::sha3_mode_e       reg_sha3_mode,       app_sha3_mode;
  sha3_pkg::keccak_strength_e reg_keccak_strength, app_keccak_strength;

  // Indicating AppIntf is active. This signal is used to check SW error
  logic app_active;

  // Command
  // sw_cmd is the command written by SW
  // checked_sw_cmd is checked in the kmac_errchk module.
  //   Invalid command is filtered out in the module.
  // kmac_cmd is generated in KeyMgr interface.
  // If SW initiates the KMAC/SHA3, kmac_cmd represents SW command,
  // if KeyMgr drives the data, kmac_cmd is controled in the state machine
  // in KeyMgr interface logic.
  kmac_cmd_e sw_cmd, checked_sw_cmd, kmac_cmd;

  // Entropy configurations
  logic [9:0]  wait_timer_prescaler;
  logic [15:0] wait_timer_limit;
  logic        entropy_seed_update;
  logic        unused_entropy_seed_upper_qe;
  logic [63:0] entropy_seed_data;
  logic        entropy_refresh_req;

  logic [HashCntW-1:0] entropy_hash_threshold;
  logic [HashCntW-1:0] entropy_hash_cnt;
  logic                entropy_hash_clr;

  logic entropy_ready;
  entropy_mode_e entropy_mode;
  logic entropy_fast_process;

  // SHA3 Error response
  sha3_pkg::err_t sha3_err;

  // KeyMgr Error response
  kmac_pkg::err_t app_err;

  // Entropy Generator Error
  kmac_pkg::err_t entropy_err;

  // Error checker
  kmac_pkg::err_t errchecker_err;

  logic err_processed;

  //////////////////////////////////////
  // Connecting Register IF to logics //
  //////////////////////////////////////

  // Function-name N and Customization input string S
  always_comb begin
    for (int i = 0 ; i < NumWordsPrefix; i++) begin
      reg_ns_prefix[32*i+:32] = reg2hw.prefix[i].q;
    end
  end

  // Command signals
  assign sw_cmd = (reg2hw.cmd.cmd.qe) ? kmac_cmd_e'(reg2hw.cmd.cmd.q) : CmdNone;
  `ASSERT_KNOWN(KmacCmd_A, sw_cmd)
  always_comb begin
    sha3_start = 1'b 0;
    sha3_run = 1'b 0;
    sha3_done = 1'b 0;
    reg2msgfifo_process = 1'b 0;

    unique case (kmac_cmd)
      CmdStart: begin
        sha3_start = 1'b 1;
      end

      CmdProcess: begin
        reg2msgfifo_process = 1'b 1;
      end

      CmdManualRun: begin
        sha3_run = 1'b 1;
      end

      CmdDone: begin
        sha3_done = 1'b 1;
      end

      CmdNone: begin
        // inactive state
      end

      default: begin
      end
    endcase
  end

  // Status register ==========================================================
  // status.squeeze is valid only when SHA3 engine completes the Absorb and not
  // running the manual keccak rounds. This status is for SW to determine when
  // to read the STATE values.
  assign hw2reg.status.sha3_idle.d     = sha3_fsm == sha3_pkg::StIdle;
  assign hw2reg.status.sha3_absorb.d   = sha3_fsm == sha3_pkg::StAbsorb;
  assign hw2reg.status.sha3_squeeze.d  = sha3_fsm == sha3_pkg::StSqueeze;

  // FIFO related status
  assign hw2reg.status.fifo_depth.d[MsgFifoDepthW-1:0] = msgfifo_depth;
  if ($bits(hw2reg.status.fifo_depth.d) != MsgFifoDepthW) begin : gen_fifo_depth_tie
    assign hw2reg.status.fifo_depth.d[$bits(hw2reg.status.fifo_depth.d)-1:MsgFifoDepthW] = '0;
  end
  assign hw2reg.status.fifo_empty.d  = msgfifo_empty;
  assign hw2reg.status.fifo_full.d   = msgfifo_full;

  // Configuration Register
  logic engine_stable;
  assign engine_stable = sha3_fsm == sha3_pkg::StIdle;

  assign hw2reg.cfg_regwen.d = engine_stable;

  // Secret Key
  // Secret key is defined as external register. So the logic latches when SW
  // writes to KEY_SHARE0 , KEY_SHARE1 registers.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sw_key_data[0] <= '0;
    end else if (engine_stable) begin
      for (int j = 0 ; j < MaxKeyLen/32 ; j++) begin
        if (reg2hw.key_share0[j].qe) begin
          sw_key_data[0][32*j+:32] <= reg2hw.key_share0[j].q;
        end
      end // for j
    end // else if engine_stable
  end // always_ff

  if (EnMasking) begin : gen_key_masked
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        sw_key_data[1] <= '0;
      end else if (engine_stable) begin
        for (int i = 0 ; i < MaxKeyLen/32 ; i++) begin
          if (reg2hw.key_share1[i].qe) begin
            sw_key_data[1][32*i+:32] <= reg2hw.key_share1[i].q;
          end
        end // for i
      end // else if engine_stable
    end // always_ff
  end else begin : gen_unused_key_share1
    logic unused_keyshare1;
    assign unused_keyshare1 = ^reg2hw.key_share1;
  end

  assign sw_key_len = key_len_e'(reg2hw.key_len.q);

  // Entropy configurations
  assign wait_timer_prescaler = reg2hw.entropy_period.prescaler.q;
  assign wait_timer_limit     = reg2hw.entropy_period.wait_timer.q;

  // Seed updated when the software writes Entropy Seed [31:0]
  assign unused_entropy_seed_upper_qe = reg2hw.entropy_seed_upper.qe;
  assign entropy_seed_update = reg2hw.entropy_seed_lower.qe ;
  assign entropy_seed_data = { reg2hw.entropy_seed_lower.q,
                               reg2hw.entropy_seed_upper.q};
  assign entropy_refresh_req = reg2hw.cmd.entropy_req.q
                            && reg2hw.cmd.entropy_req.qe;

  assign entropy_hash_threshold = reg2hw.entropy_refresh.threshold.q;
  assign hw2reg.entropy_refresh.hash_cnt.de = 1'b 1;
  assign hw2reg.entropy_refresh.hash_cnt.d  = entropy_hash_cnt;

  assign entropy_hash_clr = reg2hw.cmd.hash_cnt_clr.qe
                         && reg2hw.cmd.hash_cnt_clr.q;

  // Entropy config
  assign entropy_ready = reg2hw.cfg.entropy_ready.q;
  assign entropy_mode  = entropy_mode_e'(reg2hw.cfg.entropy_mode.q);
  assign entropy_fast_process = reg2hw.cfg.entropy_fast_process.q;

  assign hw2reg.cfg.entropy_ready.de = entropy_ready;
  assign hw2reg.cfg.entropy_ready.d = 1'b 0; // always clear when ready

  `ASSERT(EntropyReadyLatched_A, $rose(entropy_ready) |=> !entropy_ready)

  // Idle control (registered output)
  // The logic checks idle of SHA3 engine, MSG_FIFO, KMAC_CORE, KEYMGR interface
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      idle_o <= 1'b 1;
    end else if ((sha3_fsm == sha3_pkg::StIdle) && msgfifo_empty) begin
      idle_o <= 1'b 1;
    end else begin
      idle_o <= 1'b 0;
    end
  end

  // Clear the error processed
  assign err_processed = reg2hw.cfg.err_processed.q;
  assign hw2reg.cfg.err_processed.de = err_processed;
  assign hw2reg.cfg.err_processed.d = 1'b 0;

  // Make sure the field has latch in reg_top
  `ASSERT(ErrProcessedLatched_A, $rose(err_processed) |=> !err_processed)

  // App mode, strength, kmac_en
  assign reg_kmac_en         = reg2hw.cfg.kmac_en.q;
  assign reg_sha3_mode       = sha3_pkg::sha3_mode_e'(reg2hw.cfg.mode.q);
  assign reg_keccak_strength = sha3_pkg::keccak_strength_e'(reg2hw.cfg.kstrength.q);

  ///////////////
  // Interrupt //
  ///////////////

  logic event_msgfifo_empty, msgfifo_empty_q;

  // Hash process absorbed interrupt
  prim_intr_hw #(.Width(1)) intr_kmac_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_absorbed),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.kmac_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.kmac_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.kmac_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.kmac_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.kmac_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.kmac_done.d),
    .intr_o                 (intr_kmac_done_o)
  );

  `ASSERT(Sha3AbsorbedPulse_A, $rose(sha3_absorbed) |=> !sha3_absorbed)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) msgfifo_empty_q <= 1'b1;
    else         msgfifo_empty_q <= msgfifo_empty;
  end

  assign event_msgfifo_empty = ~msgfifo_empty_q & msgfifo_empty;

  prim_intr_hw #(.Width(1)) intr_fifo_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_msgfifo_empty),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.fifo_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.fifo_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.fifo_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.fifo_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.fifo_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.fifo_empty.d),
    .intr_o                 (intr_fifo_empty_o)
  );

  // Error
  // As of now, only SHA3 error exists. More error codes will be added.

  logic event_error;
  assign event_error = sha3_err.valid    | app_err.valid
                     | entropy_err.valid | errchecker_err.valid;

  // Assing error code to the register
  assign hw2reg.err_code.de = event_error;

  always_comb begin
    hw2reg.err_code.d = '0;

    priority case (1'b 1)
      // app_err has the highest priority. If SW issues an incorrect command
      // while app is in active state, the error from AppIntf is passed
      // through.
      app_err.valid: begin
        hw2reg.err_code.d = {app_err.code, app_err.info};
      end

      errchecker_err.valid: begin
        hw2reg.err_code.d = {errchecker_err.code , errchecker_err.info};
      end

      sha3_err.valid: begin
        hw2reg.err_code.d = {sha3_err.code , sha3_err.info};
      end

      entropy_err.valid: begin
        hw2reg.err_code.d = {entropy_err.code, entropy_err.info};
      end

      default: begin
        hw2reg.err_code.d = '0;
      end
    endcase
  end

  prim_intr_hw #(.Width(1)) intr_kmac_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_error),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.kmac_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.kmac_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.kmac_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.kmac_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.kmac_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.kmac_err.d),
    .intr_o                 (intr_kmac_err_o)
  );

  ///////////////////
  // State Machine //
  ///////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      kmac_st <= KmacIdle;
    end else begin
      kmac_st <= kmac_st_d;
    end
  end

  always_comb begin
    // Default value
    kmac_st_d = KmacIdle;

    entropy_in_keyblock = 1'b 0;

    unique case (kmac_st)
      KmacIdle: begin
        if (kmac_cmd == CmdStart) begin
          // If cSHAKE turned on
          if (sha3_pkg::CShake == app_sha3_mode) begin
            kmac_st_d = KmacPrefix;
          end else begin
            // Jump to Msg feed directly
            kmac_st_d = KmacMsgFeed;
          end
        end else begin
          kmac_st_d = KmacIdle;
        end
      end

      KmacPrefix: begin
        // Wait until SHA3 processes one block
        if (sha3_block_processed) begin
          kmac_st_d = (app_kmac_en) ? KmacKeyBlock : KmacMsgFeed ;
        end else begin
          kmac_st_d = KmacPrefix;
        end
      end

      KmacKeyBlock: begin
        entropy_in_keyblock = 1'b 1;
        if (sha3_block_processed) begin
          kmac_st_d = KmacMsgFeed;
        end else begin
          kmac_st_d = KmacKeyBlock;
        end
      end

      KmacMsgFeed: begin
        // If absorbed, move to Digest
        if (sha3_absorbed && sha3_done) begin
          // absorbed and done can be asserted at a cycle if Applications have
          // requested the hash operation. kmac_app FSM issues CmdDone command
          // if it receives absorbed signal.
          kmac_st_d = KmacIdle;
        end else if (sha3_absorbed && !sha3_done) begin
          kmac_st_d = KmacDigest;
        end else begin
          kmac_st_d = KmacMsgFeed;
        end
      end

      KmacDigest: begin
        // SW can manually run it, wait till done
        if (sha3_done) begin
          kmac_st_d = KmacIdle;
        end else begin
          kmac_st_d = KmacDigest;
        end
      end

      default: begin
        kmac_st_d = KmacIdle;
      end
    endcase
  end
  `ASSERT_KNOWN(KmacStKnown_A, kmac_st)

  ///////////////
  // Instances //
  ///////////////

  // KMAC core
  kmac_core #(
    .EnMasking (EnMasking)
  ) u_kmac_core (
    .clk_i,
    .rst_ni,

    // from Msg FIFO
    .fifo_valid_i (msgfifo_valid),
    .fifo_data_i  (msgfifo_data ),
    .fifo_strb_i  (msgfifo_strb ),
    .fifo_ready_o (msgfifo_ready),

    // to SHA3 core
    .msg_valid_o  (msg_valid),
    .msg_data_o   (msg_data ),
    .msg_strb_o   (msg_strb ),
    .msg_ready_i  (msg_ready),

    // Configurations
    .kmac_en_i  (app_kmac_en),
    .mode_i     (app_sha3_mode),
    .strength_i (app_keccak_strength),

    // Secret key interface
    .key_data_i (key_data),
    .key_len_i  (key_len ),

    // Controls
    .start_i   (sha3_start          ),
    .process_i (msgfifo2kmac_process),
    .done_i    (sha3_done           ),
    .process_o (kmac2sha3_process   )
  );

  // SHA3 hashing engine
  sha3 #(
    .EnMasking (EnMasking),
    .ReuseShare (ReuseShare)
  ) u_sha3 (
    .clk_i,
    .rst_ni,

    // MSG_FIFO interface (or from KMAC)
    .msg_valid_i (msg_valid),
    .msg_data_i  (msg_data ), // always store to 0 regardless of EnMasking
    .msg_strb_i  (msg_strb ),
    .msg_ready_o (msg_ready),

    // Entropy interface
    .rand_valid_i    (sha3_rand_valid),
    .rand_data_i     (sha3_rand_data),
    .rand_consumed_o (sha3_rand_consumed),

    // N, S: Used in cSHAKE mode
    .ns_data_i       (ns_prefix),

    // Configurations
    .mode_i     (app_sha3_mode),
    .strength_i (app_keccak_strength),

    // Controls (CMD register)
    .start_i    (sha3_start       ),
    .process_i  (kmac2sha3_process),
    .run_i      (sha3_run         ),
    .done_i     (sha3_done        ),

    .absorbed_o  (sha3_absorbed),
    .squeezing_o (unused_sha3_squeeze),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o (state_valid),
    .state_o       (state), // [Share]

    .error_o (sha3_err)
  );

  // MSG_FIFO window interface to FIFO interface ===============================
  // Tie the read path
  assign tlram_rvalid = 1'b 0;
  assign tlram_rdata = '0;
  assign tlram_rerror = '0;

  // Convert endian here
  //    prim_packer always packs to the right(bit0). If the input DWORD is
  //    big-endian, it needs to be swapped to little-endian to maintain the
  //    order. Internal SHA3(Keccak) runs in little-endian in contrast to HMAC
  //    So, no endian-swap after prim_packer.
  assign tlram_wdata_endian = conv_endian32(tlram_wdata, reg2hw.cfg.msg_endianness.q);
  assign tlram_wmask_endian = conv_endian32(tlram_wmask, reg2hw.cfg.msg_endianness.q);

  // TL Adapter
  tlul_adapter_sram #(
    .SramAw ($clog2(MsgWindowDepth)),
    .SramDw (MsgWindowWidth),
    .Outstanding (1),
    .ByteAccess  (1),
    .ErrOnRead   (1)
  ) u_tlul_adapter_msgfifo (
    .clk_i,
    .rst_ni,
    .en_ifetch_i (tlul_pkg::InstrDis),
    .tl_i        (tl_win_h2d[WinMsgFifo]),
    .tl_o        (tl_win_d2h[WinMsgFifo]),

    .req_o       (tlram_req),
    .req_type_o  (),
    .gnt_i       (tlram_gnt),
    .we_o        (tlram_we ),
    .addr_o      (tlram_addr),
    .wdata_o     (tlram_wdata),
    .wmask_o     (tlram_wmask),
    .intg_error_o(           ),
    .rdata_i     (tlram_rdata),
    .rvalid_i    (tlram_rvalid),
    .rerror_i    (tlram_rerror)
  );

  assign sw_msg_valid = tlram_req & tlram_we ;
  if (MsgWidth == MsgWindowWidth) begin : gen_sw_msg_samewidth
    assign sw_msg_data  = tlram_wdata_endian ;
    assign sw_msg_mask  = tlram_wmask_endian ;
  end else begin : gen_sw_msg_diff
    assign sw_msg_data = {{MsgWidth-MsgWindowWidth{1'b0}}, tlram_wdata_endian};
    assign sw_msg_mask = {{MsgWidth-MsgWindowWidth{1'b0}}, tlram_wmask_endian};
  end
  assign tlram_gnt    = sw_msg_ready ;

  logic unused_tlram_addr;
  assign unused_tlram_addr = &{1'b0, tlram_addr};

  // Application interface Mux/Demux
  kmac_app #(
    .EnMasking(EnMasking)
  ) u_app_intf (
    .clk_i,
    .rst_ni,

    .reg_key_data_i (sw_key_data),
    .reg_key_len_i  (sw_key_len),

    .reg_prefix_i (reg_ns_prefix),

    .reg_kmac_en_i         (reg_kmac_en),
    .reg_sha3_mode_i       (reg_sha3_mode),
    .reg_keccak_strength_i (reg_keccak_strength),

    // data from tl_adapter
    .sw_valid_i (sw_msg_valid),
    .sw_data_i  (sw_msg_data),
    .sw_mask_i  (sw_msg_mask),
    .sw_ready_o (sw_msg_ready),

    // KeyMgr sideloaded key interface
    .keymgr_key_i,

    // Application data in / digest out interface
    .app_i,
    .app_o,

    // Secret Key output to KMAC Core
    .key_data_o (key_data),
    .key_len_o  (key_len),

    // to MSG_FIFO
    .kmac_valid_o (mux2fifo_valid),
    .kmac_data_o  (mux2fifo_data),
    .kmac_mask_o  (mux2fifo_mask),
    .kmac_ready_i (mux2fifo_ready),

    // to KMAC Core
    .kmac_en_o (app_kmac_en),

    // to SHA3 Core
    .sha3_prefix_o     (ns_prefix),
    .sha3_mode_o       (app_sha3_mode),
    .keccak_strength_o (app_keccak_strength),

    // Keccak state from SHA3 core
    .keccak_state_valid_i (state_valid),
    .keccak_state_i       (state),

    // to STATE TL Window
    .reg_state_valid_o    (unused_reg_state_valid),
    .reg_state_o          (reg_state),

    // Configuration: Sideloaded Key
    .keymgr_key_en_i      (reg2hw.cfg.sideload.q),

    .absorbed_i (sha3_absorbed), // from SHA3
    .absorbed_o (event_absorbed), // to SW

    .app_active_o(app_active),

    .error_i         (sha3_err.valid),
    .err_processed_i (err_processed),

    // Command interface
    .sw_cmd_i (checked_sw_cmd),
    .cmd_o    (kmac_cmd),

    // Error report
    .error_o (app_err)

  );

  // Message FIFO
  kmac_msgfifo #(
    .OutWidth (kmac_pkg::MsgWidth),
    .MsgDepth (kmac_pkg::MsgFifoDepth)
  ) u_msgfifo (
    .clk_i,
    .rst_ni,

    .fifo_valid_i (mux2fifo_valid),
    .fifo_data_i  (mux2fifo_data),
    .fifo_mask_i  (mux2fifo_mask),
    .fifo_ready_o (mux2fifo_ready),

    .msg_valid_o (msgfifo_valid),
    .msg_data_o  (msgfifo_data[0]),
    .msg_strb_o  (msgfifo_strb),
    .msg_ready_i (msgfifo_ready),

    .fifo_empty_o (msgfifo_empty), // intr and status
    .fifo_full_o  (msgfifo_full),  // connected to status only
    .fifo_depth_o (msgfifo_depth),

    .clear_i (sha3_done),

    .process_i (reg2msgfifo_process ),
    .process_o (msgfifo2kmac_process)
  );

  // State (Digest) reader
  kmac_staterd #(
    .AddrW     (9), // 512B
    .EnMasking (EnMasking)
  ) u_staterd (
    .clk_i,
    .rst_ni,

    .tl_i (tl_win_h2d[WinState]),
    .tl_o (tl_win_d2h[WinState]),

    .state_i (reg_state),

    .endian_swap_i (reg2hw.cfg.state_endianness.q)
  );

  // Error checker
  kmac_errchk u_errchk (
    .clk_i,
    .rst_ni,

    // Configurations
    .cfg_mode_i    (reg_sha3_mode      ),
    .cfg_strength_i(reg_keccak_strength),

    .kmac_en_i      (reg_kmac_en        ),
    .cfg_prefix_6B_i(reg_ns_prefix[47:0]), // first 6B of PREFIX

    // SW commands
    .sw_cmd_i(sw_cmd),
    .sw_cmd_o(checked_sw_cmd),

    // Status from KMAC_APP
    .app_active_i(app_active),

    // Status from SHA3 core
    .sha3_absorbed_i(sha3_absorbed       ),
    .keccak_done_i  (sha3_block_processed),

    .error_o(errchecker_err)
  );

  // Entropy Generator
  if (EnMasking == 1) begin : gen_entropy
    logic entropy_req, entropy_ack, entropy_fips;
    logic [MsgWidth-1:0] entropy_data;
    logic unused_entropy_fips;
    assign unused_entropy_fips = entropy_fips;

    // EDN Request
    prim_edn_req #(
      .OutWidth   (MsgWidth),
      .MaxLatency (500000)  // 5ms expected
    ) u_edn_req (
      // Design side
      .clk_i,
      .rst_ni,
      .req_chk_i (1'b1),
      .req_i     (entropy_req),
      .ack_o     (entropy_ack),
      .data_o    (entropy_data),
      .fips_o    (entropy_fips),
      // EDN side
      .clk_edn_i,
      .rst_edn_ni,
      .edn_o (entropy_o),
      .edn_i (entropy_i)
    );

    kmac_entropy #(
     .RndCnstLfsrPerm(RndCnstLfsrPerm)
    ) u_entropy (
      .clk_i,
      .rst_ni,

      // EDN interface
      .entropy_req_o (entropy_req),
      .entropy_ack_i (entropy_ack),
      .entropy_data_i(entropy_data),

      // Entropy to internal logic (DOM AND)
      .rand_valid_o    (sha3_rand_valid),
      .rand_data_o     (sha3_rand_data),
      .rand_consumed_i (sha3_rand_consumed),

      // Status from internal logic
      //// KMAC secret block handling indicator
      .in_keyblock_i (entropy_in_keyblock),

      // Configuration
      .mode_i          (entropy_mode),
      .entropy_ready_i (entropy_ready),
      .fast_process_i  (entropy_fast_process),

      //// Entropy refresh period in clk cycles
      .wait_timer_prescaler_i (wait_timer_prescaler),
      .wait_timer_limit_i     (wait_timer_limit),

      //// SW update of seed
      .seed_update_i         (entropy_seed_update),
      .seed_data_i           (entropy_seed_data),
      .entropy_refresh_req_i (entropy_refresh_req),

      // Status
      .hash_cnt_o       (entropy_hash_cnt),
      .hash_cnt_clr_i   (entropy_hash_clr),
      .hash_threshold_i (entropy_hash_threshold),

      // Error
      .err_o           (entropy_err),
      .err_processed_i (err_processed)
    );
  end else begin : gen_empty_entropy
    // If Masking is not used, no need of entropy. Ignore inputs and config; tie output to 0.
    edn_pkg::edn_rsp_t unused_entropy_input;
    entropy_mode_e     unused_entropy_mode;
    logic              unused_entropy_fast_process;

    assign unused_entropy_input        = entropy_i;
    assign unused_entropy_mode         = entropy_mode;
    assign unused_entropy_fast_process = entropy_fast_process;

    assign entropy_o = '{default: '0};

    logic unused_sha3_rand_consumed;
    assign sha3_rand_valid = 1'b 1;
    assign sha3_rand_data = '0;
    assign unused_sha3_rand_consumed = sha3_rand_consumed;

    logic unused_seed_update;
    logic [63:0] unused_seed_data;
    logic [31:0] unused_refresh_period;
    logic unused_entropy_refresh_req;
    assign unused_seed_data = entropy_seed_data;
    assign unused_seed_update = entropy_seed_update;
    assign unused_refresh_period = ^{wait_timer_limit, wait_timer_prescaler};
    assign unused_entropy_refresh_req = entropy_refresh_req;

    logic unused_entropy_hash;
    assign unused_entropy_hash = ^{entropy_hash_clr, entropy_hash_threshold};
    assign entropy_hash_cnt = '0;

    assign entropy_err = '{valid: 1'b 0, code: ErrNone, info: '0};

    logic [1:0] unused_entropy_status;
    assign unused_entropy_status = entropy_in_keyblock;
  end

  // Register top
  logic [NumAlerts-1:0] alert_test, alerts;
  kmac_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .tl_win_o (tl_win_h2d),
    .tl_win_i (tl_win_d2h),

    .reg2hw,
    .hw2reg,
    .intg_err_o(alerts[0]),
    .devmode_i (devmode)
  );

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  assign en_masking_o = EnMasking;

  ////////////////
  // Assertions //
  ////////////////

  // Assert known for output values
  `ASSERT_KNOWN(KmacDone_A, intr_kmac_done_o)
  `ASSERT_KNOWN(FifoEmpty_A, intr_fifo_empty_o)
  `ASSERT_KNOWN(KmacErr_A, intr_kmac_err_o)
  `ASSERT_KNOWN(TlODValidKnown_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown_A, tl_o.a_ready)
  `ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)
  `ASSERT_KNOWN(EnMaskingKnown_A, en_masking_o)

  // Parameter as desired
  `ASSERT_INIT(SecretKeyDivideBy32_A, (kmac_pkg::MaxKeyLen % 32) == 0)

  // Command input should be onehot0
  `ASSUME(CmdOneHot0_M, reg2hw.cmd.cmd.qe |-> $onehot0(reg2hw.cmd.cmd.q))
endmodule
