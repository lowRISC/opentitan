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

  // Command delay, useful for SCA measurements only. A value of e.g. 40 allows the processor to go
  // into sleep before KMAC starts operation. If a value > 0 is chosen, the processor can provide
  // two commands subsquently and then go to sleep. The second command is buffered internally and
  // will be presented to the hardware SecCmdDelay number of cycles after the first one.
  parameter int SecCmdDelay = 0,

  // Accept SW message when idle and before receiving a START command. Useful for SCA only.
  parameter bit SecIdleAcceptSwMsg = 1'b0,

  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,

  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,

  input rst_shadowed_ni,

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

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

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
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 6 -n 6 \
  //      -s 1966361510 --language=sv
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
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    // Idle state
    KmacIdle = 6'b001011,

    // When software writes CmdStart @ KmacIdle and kmac_en, FSM moves to this
    KmacPrefix = 6'b000110,

    // When SHA3 engine processes Key block, FSM moves to here.
    KmacKeyBlock = 6'b111110,

    // Message Feed
    KmacMsgFeed = 6'b010101,

    // Complete and squeeze
    KmacDigest = 6'b101101,

    // Error
    KmacTerminalError = 6'b110000

  } kmac_st_e;

  logic [StateWidth-1:0] kmac_st_raw;
  kmac_st_e              kmac_st, kmac_st_d;

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
  kmac_cmd_e sw_cmd, checked_sw_cmd, kmac_cmd, cmd_q;
  logic      cmd_update;

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

  logic alert_fatal, alert_recov_operation;
  logic alert_intg_err;

  // Life cycle
  lc_ctrl_pkg::lc_tx_t  lc_escalate_en_sync, lc_escalate_en;

  //////////////////////////////////////
  // Connecting Register IF to logics //
  //////////////////////////////////////

  // Function-name N and Customization input string S
  always_comb begin
    for (int i = 0 ; i < NumWordsPrefix; i++) begin
      reg_ns_prefix[32*i+:32] = reg2hw.prefix[i].q;
    end
  end

  if (SecCmdDelay > 0) begin : gen_cmd_delay_buf
    // Delay and buffer commands for SCA measurements.
    localparam int unsigned WidthCounter = $clog2(SecCmdDelay+1);
    logic [WidthCounter-1:0] count_d, count_q;
    logic                    counting_d, counting_q;
    logic                    cmd_buf_empty;
    kmac_cmd_e               cmd_buf_q;

    assign cmd_buf_empty = (cmd_buf_q == CmdNone);

    // When seeing a write to the cmd register, we start counting. We stop counting once the
    // counter has expired and the command buffer is empty.
    assign counting_d = reg2hw.cmd.cmd.qe          ? 1'b1 :
                        cmd_update & cmd_buf_empty ? 1'b0 : counting_q;

    // Clear counter upon writes to the cmd register or if the specified delay is reached.
    assign count_d = reg2hw.cmd.cmd.qe ? '0             :
                     cmd_update        ? '0             :
                     counting_q        ? count_q + 1'b1 : count_q;

    // The manual run command cannot be delayed. Software expects this to be triggered immediately
    // and will poll the status register to wait for the SHA3 engine to return back to the squeeze
    // state.
    assign cmd_update = (cmd_q == CmdManualRun)                    ? 1'b1 :
                        (count_q == SecCmdDelay[WidthCounter-1:0]) ? 1'b1 : 1'b0;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        count_q    <= '0;
        counting_q <= 1'b0;
      end else begin
        count_q    <= count_d;
        counting_q <= counting_d;
      end
    end

    // cmd.q is valid while cmd.qe is high, meaning it needs to be registered. We buffer one
    // additional command such that software can write START followed by PROCESS and then go to
    // sleep.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cmd_q     <= CmdNone;
        cmd_buf_q <= CmdNone;
      end else begin
        if (reg2hw.cmd.cmd.qe && cmd_update) begin
          // New write & counter expired.
          cmd_q     <= cmd_buf_q;
          cmd_buf_q <= kmac_cmd_e'(reg2hw.cmd.cmd.q);

        end else if (reg2hw.cmd.cmd.qe) begin
          // New write.
          if (counting_q == 1'b0) begin
            cmd_q     <= kmac_cmd_e'(reg2hw.cmd.cmd.q);
          end else begin
            cmd_buf_q <= kmac_cmd_e'(reg2hw.cmd.cmd.q);
          end

        end else if (cmd_update) begin
          // Counter expired.
          cmd_q     <= cmd_buf_q;
          cmd_buf_q <= CmdNone;
        end
      end
    end

    // Create a lint error to reduce the risk of accidentally enabling this feature.
    logic sec_cmd_delay_dummy;
    assign sec_cmd_delay_dummy = cmd_update;

  end else begin : gen_no_cmd_delay_buf
    // Directly forward signals from register IF.
    assign cmd_update = reg2hw.cmd.cmd.qe;
    assign cmd_q      = kmac_cmd_e'(reg2hw.cmd.cmd.q);
  end

  // Command signals
  assign sw_cmd = (cmd_update) ? cmd_q : CmdNone;
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
  // SEC_CM: SW_KEY.KEY.MASKING
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
  assign entropy_ready = reg2hw.cfg_shadowed.entropy_ready.q
                       & reg2hw.cfg_shadowed.entropy_ready.qe;
  assign entropy_mode  = entropy_mode_e'(reg2hw.cfg_shadowed.entropy_mode.q);
  assign entropy_fast_process = reg2hw.cfg_shadowed.entropy_fast_process.q;

  `ASSERT(EntropyReadyLatched_A, $rose(entropy_ready) |=> !entropy_ready)

  // Idle control (registered output)
  // The logic checks idle of SHA3 engine, MSG_FIFO, KMAC_CORE, KEYMGR interface
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      idle_o <= 1'b 1;
    end else if ((sha3_fsm == sha3_pkg::StIdle) && (msgfifo_empty || SecIdleAcceptSwMsg)) begin
      idle_o <= 1'b 1;
    end else begin
      idle_o <= 1'b 0;
    end
  end

  // Clear the error processed
  assign err_processed = reg2hw.cfg_shadowed.err_processed.q
                       & reg2hw.cfg_shadowed.err_processed.qe;

  // Make sure the field has latch in reg_top
  `ASSERT(ErrProcessedLatched_A, $rose(err_processed) |=> !err_processed)

  // App mode, strength, kmac_en
  assign reg_kmac_en         = reg2hw.cfg_shadowed.kmac_en.q;
  assign reg_sha3_mode       = sha3_pkg::sha3_mode_e'(reg2hw.cfg_shadowed.mode.q);
  assign reg_keccak_strength = sha3_pkg::keccak_strength_e'(reg2hw.cfg_shadowed.kstrength.q);

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
                     | entropy_err.valid | errchecker_err.valid
                     ;

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

  // LFSR errors
  logic lfsr_error, kmac_entropy_lfsr_error;
  assign lfsr_error = kmac_entropy_lfsr_error;

  // Counter errors
  logic counter_error, sha3_count_error, key_index_error;
  assign counter_error = sha3_count_error
                       | key_index_error;

  // State Errors
  logic sparse_fsm_error;
  logic sha3_state_error, kmac_errchk_state_error;
  logic kmac_core_state_error, kmac_app_state_error;
  logic kmac_entropy_state_error, kmac_state_error;
  assign sparse_fsm_error = sha3_state_error
                          | kmac_errchk_state_error
                          | kmac_core_state_error
                          | kmac_app_state_error
                          | kmac_entropy_state_error
                          | kmac_state_error;

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

  // State FF
  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_sparse_fsm_flop #(
    .StateEnumT(kmac_st_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(KmacIdle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i (kmac_st_d),
    .state_o (kmac_st_raw)
  );
  assign kmac_st = kmac_st_e'(kmac_st_raw);

  always_comb begin
    // Default value
    kmac_st_d = KmacIdle;

    entropy_in_keyblock = 1'b 0;
    kmac_state_error = 1'b 0;

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

      KmacTerminalError: begin
        //this state is terminal
        kmac_st_d = KmacTerminalError;
        kmac_state_error = 1'b 1;
      end

      default: begin
        kmac_st_d = KmacTerminalError;
        kmac_state_error = 1'b 1;
      end
    endcase

    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_escalate_en != lc_ctrl_pkg::Off) begin
      kmac_st_d = KmacTerminalError;
    end
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
    .process_o (kmac2sha3_process   ),

    // LC escalation
    .lc_escalate_en_i (lc_escalate_en),

    // Error detection
    .sparse_fsm_error_o (kmac_core_state_error),
    .key_index_error_o  (key_index_error)
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

    // LC escalation
    .lc_escalate_en_i (lc_escalate_en),

    .absorbed_o  (sha3_absorbed),
    .squeezing_o (unused_sha3_squeeze),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o (state_valid),
    .state_o       (state), // [Share]

    .error_o            (sha3_err),
    .sparse_fsm_error_o (sha3_state_error),
    .count_error_o  (sha3_count_error)
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
  assign tlram_wdata_endian = conv_endian32(tlram_wdata,
                                reg2hw.cfg_shadowed.msg_endianness.q);
  assign tlram_wmask_endian = conv_endian32(tlram_wmask,
                                reg2hw.cfg_shadowed.msg_endianness.q);

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
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
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
    .EnMasking(EnMasking),
    .SecIdleAcceptSwMsg(SecIdleAcceptSwMsg)
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
    .keymgr_key_en_i      (reg2hw.cfg_shadowed.sideload.q),

    .absorbed_i (sha3_absorbed), // from SHA3
    .absorbed_o (event_absorbed), // to SW

    .app_active_o(app_active),

    .error_i         (sha3_err.valid),
    .err_processed_i (err_processed),

    // Command interface
    .sw_cmd_i (checked_sw_cmd),
    .cmd_o    (kmac_cmd),

    // LC escalation
    .lc_escalate_en_i (lc_escalate_en),

    // Error report
    .error_o            (app_err),
    .sparse_fsm_error_o (kmac_app_state_error)

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

    .endian_swap_i (reg2hw.cfg_shadowed.state_endianness.q)
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

    // LC escalation
    .lc_escalate_en_i (lc_escalate_en),

    .error_o            (errchecker_err),
    .sparse_fsm_error_o (kmac_errchk_state_error)
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

      // LC escalation
      .lc_escalate_en_i (lc_escalate_en),

      // Error
      .err_o              (entropy_err),
      .sparse_fsm_error_o (kmac_entropy_state_error),
      .lfsr_error_o       (kmac_entropy_lfsr_error),
      .err_processed_i    (err_processed)
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

    assign kmac_entropy_state_error = 1'b 0;
    assign kmac_entropy_lfsr_error  = 1'b 0;

    logic [1:0] unused_entropy_status;
    assign unused_entropy_status = entropy_in_keyblock;
  end

  // Register top
  logic [NumAlerts-1:0] alert_test, alerts, alerts_q;

  logic shadowed_storage_err, shadowed_update_err;
  kmac_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,

    .tl_i,
    .tl_o,

    .tl_win_o (tl_win_h2d),
    .tl_win_i (tl_win_d2h),

    .reg2hw,
    .hw2reg,

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(alert_intg_err),
    .devmode_i (devmode)
  );

  // SEC_CM: CONFIG.SHADOW
  assign shadowed_storage_err = |{
      reg2hw.cfg_shadowed.kmac_en.err_storage             ,
      reg2hw.cfg_shadowed.kstrength.err_storage           ,
      reg2hw.cfg_shadowed.mode.err_storage                ,
      reg2hw.cfg_shadowed.msg_endianness.err_storage      ,
      reg2hw.cfg_shadowed.state_endianness.err_storage    ,
      reg2hw.cfg_shadowed.sideload.err_storage            ,
      reg2hw.cfg_shadowed.entropy_mode.err_storage        ,
      reg2hw.cfg_shadowed.entropy_fast_process.err_storage,
      reg2hw.cfg_shadowed.entropy_ready.err_storage       ,
      reg2hw.cfg_shadowed.err_processed.err_storage
    };

  assign shadowed_update_err  = |{
      reg2hw.cfg_shadowed.kmac_en.err_update              ,
      reg2hw.cfg_shadowed.kstrength.err_update            ,
      reg2hw.cfg_shadowed.mode.err_update                 ,
      reg2hw.cfg_shadowed.msg_endianness.err_update       ,
      reg2hw.cfg_shadowed.state_endianness.err_update     ,
      reg2hw.cfg_shadowed.sideload.err_update             ,
      reg2hw.cfg_shadowed.entropy_mode.err_update         ,
      reg2hw.cfg_shadowed.entropy_fast_process.err_update ,
      reg2hw.cfg_shadowed.entropy_ready.err_update        ,
      reg2hw.cfg_shadowed.err_processed.err_update
    };

  logic unused_cfg_shadowed_qe;
  assign unused_cfg_shadowed_qe = ^{
    reg2hw.cfg_shadowed.kmac_en.qe              ,
    reg2hw.cfg_shadowed.kstrength.qe            ,
    reg2hw.cfg_shadowed.mode.qe                 ,
    reg2hw.cfg_shadowed.msg_endianness.qe       ,
    reg2hw.cfg_shadowed.state_endianness.qe     ,
    reg2hw.cfg_shadowed.sideload.qe             ,
    reg2hw.cfg_shadowed.entropy_mode.qe         ,
    reg2hw.cfg_shadowed.entropy_fast_process.qe
    };

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.fatal_fault_err.q
      & reg2hw.alert_test.fatal_fault_err.qe,    // [1]
    reg2hw.alert_test.recov_operation_err.q
      & reg2hw.alert_test.recov_operation_err.qe // [0]
  };

  assign alerts = {
    alert_fatal,           // Alerts[1]
    alert_recov_operation  // Alerts[0]
    };

  assign alert_recov_operation = shadowed_update_err;

  // The recoverable alert is observable via status register until the KMAC operation is restarted
  // by re-writing the Control Register.
  assign hw2reg.status.alert_recov_ctrl_update_err.d  = alert_recov_operation;

  assign alert_fatal = shadowed_storage_err
                     | alert_intg_err
                     | sparse_fsm_error
                     | counter_error
                     | lfsr_error
                     ;

  // Make the fatal alert observable via status register.
  assign hw2reg.status.alert_fatal_fault.d  = alert_fatal;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
  // break up the combinatorial path for local escalation
    if (!rst_ni) begin
      alerts_q[1] <= 1'b0;
    end else if (alerts[1]) begin
      // fatal alerts cannot be cleared
      alerts_q[1] <= 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
  // break up the combinatorial path for local escalation
    if (!rst_ni) begin
      alerts_q[0] <= 1'b0;
    end else begin
      // recoverable alerts can be cleared so just latch the value
      alerts_q[0] <= alerts[0];
    end
  end

  lc_ctrl_pkg::lc_tx_t alert_to_lc_tx;
  assign alert_to_lc_tx = lc_ctrl_pkg::lc_tx_bool_to_lc_tx(alerts_q[1]);
  assign lc_escalate_en = lc_ctrl_pkg::lc_tx_or_hi(alert_to_lc_tx, lc_escalate_en_sync);

  // Synchronize life cycle input
  prim_lc_sync #(
    .NumCopies (1)
  ) u_prim_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i ( lc_escalate_en_i    ),
    .lc_en_o ( lc_escalate_en_sync )
  );

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

`ifndef SYNTHESIS
  // redundant counter error
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(SentMsgCountCheck_A, u_sha3.u_pad.u_sentmsg_count,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RoundCountCheck_A, u_sha3.u_keccak.u_round_count,
                                         alert_tx_o[1])
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(KeyIndexCountCheck_A, u_kmac_core.u_key_index_count,
                                         alert_tx_o[1])
  // Sparse FSM state error
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KmacCoreFsmCheck_A, u_kmac_core.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KmacAppFsmCheck_A, u_app_intf.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3FsmCheck_A, u_sha3.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3padFsmCheck_A, u_sha3.u_pad.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KeccackFsmCheck_A, u_sha3.u_keccak.u_state_regs,
                                       alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(ErrorCheckFsmCheck_A, u_errchk.u_state_regs, alert_tx_o[1])
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KmacFsmCheck_A, u_state_regs, alert_tx_o[1])

  // prim is only instantiated if masking is enabled
  if (EnMasking == 1) begin : g_testassertion
    `ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(EntropyFsmCheck_A, gen_entropy.u_entropy.u_state_regs,
                                         alert_tx_o[1])
    // Alert assertions for double LFSR.
    `ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ALERT(DoubleLfsrCheck_A,
        gen_entropy.u_entropy.u_lfsr, alert_tx_o[1])
  end
`endif
endmodule
