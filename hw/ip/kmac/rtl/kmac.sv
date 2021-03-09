// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC/SHA3

`include "prim_assert.sv"

module kmac
  import kmac_pkg::*;
#(
  // EnMasking: Enable masking security hardening inside keccak_round
  // If it is enabled, the result digest will be two set of 1600bit.
  parameter bit EnMasking = 1,

  // ReuseShare: If set, keccak_round logic only consumes small portion of
  // entropy, not 1600bit of entropy at every round. It uses adjacent shares
  // as entropy inside Domain-Oriented Masking AND logic.
  // This parameter only affects when `EnMasking` is set.
  parameter bit ReuseShare = 0
) (
  input clk_i,
  input rst_ni,

  input clk_edn_i,
  input rst_edn_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // KeyMgr sideload (secret key) interface
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // KeyMgr KDF data path
  input  keymgr_pkg::kmac_data_req_t keymgr_kdf_i,
  output keymgr_pkg::kmac_data_rsp_t keymgr_kdf_o,

  // EDN interface
  output edn_pkg::edn_req_t entropy_o,
  input  edn_pkg::edn_rsp_t entropy_i,

  // interrupts
  output logic intr_kmac_done_o,
  output logic intr_fifo_empty_o,
  output logic intr_kmac_err_o,

  // Idle signal
  output logic idle_o
);

  import kmac_reg_pkg::*;

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

  // devmode signals comes from LifeCycle.
  // TODO: Implement
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
  logic entropy_in_progress, entropy_in_keyblock;

  // KeyMgr interface logic generates event_absorbed from sha3_absorbed.
  // It is active only if SW initiates the hashing engine.
  logic event_absorbed;

  sha3_pkg::sha3_st_e sha3_fsm;

  // Prefix: kmac_pkg defines Prefix based on N size and S size.
  // Then computes left_encode(len(N)) size and left_encode(len(S))
  // For given default value 32, 256 bits, the max
  // encode_string(N) || encode_string(S) is 328. So 11 Prefix registers are
  // created.
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

  // Command
  // sw_cmd is the command written by SW
  // kmac_cmd is generated in KeyMgr interface.
  // If SW initiates the KMAC/SHA3, kmac_cmd represents SW command,
  // if KeyMgr drives the data, kmac_cmd is controled in the state machine
  // in KeyMgr interface logic.
  kmac_cmd_e sw_cmd, kmac_cmd;

  // Entropy configurations
  logic [15:0] entropy_timer_limit;
  logic [15:0] wait_timer_limit;
  logic        entropy_seed_update;
  logic        unused_entropy_seed_upper_qe;
  logic [63:0] entropy_seed_data;

  logic entropy_ready;
  entropy_mode_e entropy_mode;
  logic entropy_fast_process;

  // SHA3 Error response
  sha3_pkg::err_t sha3_err;

  // KeyMgr Error response
  kmac_pkg::err_t keymgr_err;

  // Entropy Generator Error
  kmac_pkg::err_t entropy_err;

  logic err_processed;

  //////////////////////////////////////
  // Connecting Register IF to logics //
  //////////////////////////////////////

  // Function-name N and Customization input string S
  always_comb begin
    for (int i = 0 ; i < NumWordsPrefix; i++) begin
      ns_prefix[32*i+:32] = reg2hw.prefix[i].q;
    end
  end

  // Command signals
  // TODO: Make the entire logic to use enum rather than signal
  assign sw_cmd = (reg2hw.cmd.qe) ? kmac_cmd_e'(reg2hw.cmd.q) : CmdNone;
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
        // TODO: Raise an error here
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
  // TODO: handle if register width of `depth` is not same to MsgFifoDepthW
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
  assign entropy_timer_limit = reg2hw.entropy_period.entropy_timer.q;
  assign wait_timer_limit    = reg2hw.entropy_period.wait_timer.q;

  // Seed updated when the software writes Entropy Seed [31:0]
  assign unused_entropy_seed_upper_qe = reg2hw.entropy_seed_upper.qe;
  assign entropy_seed_update = reg2hw.entropy_seed_lower.qe ;
  assign entropy_seed_data = { reg2hw.entropy_seed_lower.q,
                               reg2hw.entropy_seed_upper.q};

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
  assign event_error =  sha3_err.valid | keymgr_err.valid | entropy_err.valid;

  // Assing error code to the register
  assign hw2reg.err_code.de = event_error;

  always_comb begin
    if (sha3_err.valid) begin
      hw2reg.err_code.d = {sha3_err.code , sha3_err.info};
    end else if (keymgr_err.valid) begin
      hw2reg.err_code.d = {keymgr_err.code, keymgr_err.info};
    end else if (entropy_err.valid) begin
      hw2reg.err_code.d = {entropy_err.code, entropy_err.info};
    end else begin
      hw2reg.err_code.d = '0;
    end
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

    entropy_in_progress = 1'b 0;
    entropy_in_keyblock = 1'b 0;

    unique case (kmac_st)
      KmacIdle: begin
        if (kmac_cmd == CmdStart) begin
          // If cSHAKE turned on
          if (sha3_pkg::CShake == sha3_pkg::sha3_mode_e'(reg2hw.cfg.mode.q)) begin
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
        entropy_in_progress =1'b 1;
        // Wait until SHA3 processes one block
        if (sha3_block_processed) begin
          kmac_st_d = (reg2hw.cfg.kmac_en.q) ? KmacKeyBlock : KmacMsgFeed ;
        end else begin
          kmac_st_d = KmacPrefix;
        end
      end

      KmacKeyBlock: begin
        entropy_in_progress = 1'b 1;
        entropy_in_keyblock = 1'b 1;
        if (sha3_block_processed) begin
          kmac_st_d = KmacMsgFeed;
        end else begin
          kmac_st_d = KmacKeyBlock;
        end
      end

      KmacMsgFeed: begin
        entropy_in_progress = 1'b 1;
        // If absorbed, move to Digest
        if (sha3_absorbed) begin
          kmac_st_d = KmacDigest;
        end else begin
          kmac_st_d = KmacMsgFeed;
        end
      end

      KmacDigest: begin
        entropy_in_progress = 1'b 1;
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
    .kmac_en_i  (reg2hw.cfg.kmac_en.q),
    .mode_i     (sha3_pkg::sha3_mode_e'(reg2hw.cfg.mode.q)),
    .strength_i (sha3_pkg::keccak_strength_e'(reg2hw.cfg.kstrength.q)),

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
    .mode_i     (sha3_pkg::sha3_mode_e'(reg2hw.cfg.mode.q)),
    .strength_i (sha3_pkg::keccak_strength_e'(reg2hw.cfg.kstrength.q)),

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
    assign sw_msg_data = {(MsgWidth-MsgWindowWidth)'(0), tlram_wdata_endian};
    assign sw_msg_mask = {(MsgWidth-MsgWindowWidth)'(0), tlram_wmask_endian};
  end
  assign tlram_gnt    = sw_msg_ready ;

  // KeyMgr Mux/Demux
  kmac_keymgr #(
    .EnMasking(EnMasking)
  ) u_keymgr_intf (
    .clk_i,
    .rst_ni,

    .reg_key_data_i (sw_key_data),
    .reg_key_len_i  (sw_key_len),

    // data from tl_adapter
    .sw_valid_i (sw_msg_valid),
    .sw_data_i  (sw_msg_data),
    .sw_mask_i  (sw_msg_mask),
    .sw_ready_o (sw_msg_ready),

    // KeyMgr sideloaded key interface
    .keymgr_key_i,

    // KeyMgr data in / digest out interface
    .keymgr_data_i (keymgr_kdf_i),
    .keymgr_data_o (keymgr_kdf_o),

    // Secret Key output to KMAC Core
    .key_data_o (key_data),
    .key_len_o  (key_len),

    // to MSG_FIFO
    .kmac_valid_o (mux2fifo_valid),
    .kmac_data_o  (mux2fifo_data),
    .kmac_mask_o  (mux2fifo_mask),
    .kmac_ready_i (mux2fifo_ready),

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

    .error_i  (sha3_err.valid),

    // Command interface
    .sw_cmd_i (sw_cmd),
    .cmd_o    (kmac_cmd),

    // Error report
    .error_o (keymgr_err)

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

  // Entropy Generator
  if (EnMasking == 1) begin : gen_entropy
    logic entropy_req, entropy_ack, entropy_fips;
    logic [MsgWidth-1:0] entropy_data;
    logic unused_entropy_fips;
    assign unused_entropy_fips = entropy_fips;

    // EDN Request
    prim_edn_req #(
      .OutWidth (MsgWidth)
    ) u_edn_req (
      // Design side
      .clk_i,
      .rst_ni,
      .req_i (entropy_req),
      .ack_o (entropy_ack),
      .data_o(entropy_data),
      .fips_o(entropy_fips),
      // EDN side
      .clk_edn_i,
      .rst_edn_ni,
      .edn_o (entropy_o),
      .edn_i (entropy_i)
    );

    kmac_entropy u_entropy (
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
      //// SHA3 engine run indicator
      .in_progress_i (entropy_in_progress),
      //// KMAC secret block handling indicator
      .in_keyblock_i (entropy_in_keyblock),

      // Configuration
      .mode_i          (entropy_mode),
      .entropy_ready_i (entropy_ready),
      .fast_process_i  (entropy_fast_process),

      //// Entropy refresh period in clk cycles
      .entropy_timer_limit_i (entropy_timer_limit),
      .wait_timer_limit_i    (wait_timer_limit),

      //// SW update of seed
      .seed_update_i (entropy_seed_update),
      .seed_data_i   (entropy_seed_data),

      // Error
      .err_o (entropy_err),
      .err_processed_i (err_processed)
    );
  end else begin : gen_empty_entropy
    // If Masking is not used, no need of entropy. Tieing 0
    edn_pkg::edn_rsp_t unused_entropy_input;
    assign unused_entropy_input = entropy_i;
    assign entropy_o = '{default: '0};

    logic unused_sha3_rand_consumed;
    assign sha3_rand_valid = 1'b 1;
    assign sha3_rand_data = '0;
    assign unused_sha3_rand_consumed = sha3_rand_consumed;

    logic unused_seed_update;
    logic [63:0] unused_seed_data;
    logic [31:0] unused_refresh_period;
    assign unused_seed_data = entropy_seed_data;
    assign unused_seed_update = entropy_seed_update;
    assign unused_refresh_period = {wait_timer_limit, entropy_timer_limit};

    assign entropy_err = '{valid: 1'b 0, code: ErrNone, info: '0};

    logic [1:0] unused_entropy_status;
    assign unused_entropy_status = {entropy_in_keyblock, entropy_in_progress};
  end

  // Register top
  kmac_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .tl_win_o (tl_win_h2d),
    .tl_win_i (tl_win_d2h),

    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i (devmode)
  );

  ////////////////
  // Assertions //
  ////////////////

  // Assert known for output values
  `ASSERT_KNOWN(KmacDone_A, intr_kmac_done_o)
  `ASSERT_KNOWN(FifoEmpty_A, intr_fifo_empty_o)
  `ASSERT_KNOWN(KmacErr_A, intr_kmac_err_o)
  `ASSERT_KNOWN(TlODValidKnown_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown_A, tl_o.a_ready)

  // Parameter as desired
  `ASSERT_INIT(SecretKeyDivideBy32_A, (kmac_pkg::MaxKeyLen % 32) == 0)

  // Command input should be onehot0
  `ASSUME(CmdOneHot0_M, reg2hw.cmd.qe |-> $onehot0(reg2hw.cmd.q))
endmodule
