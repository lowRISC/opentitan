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
  parameter int EnMasking = 0,

  // ReuseShare: If set, keccak_round logic only consumes small portion of
  // entropy, not 1600bit of entropy at every round. It uses adjacent shares
  // as entropy inside Domain-Oriented Masking AND logic.
  // This parameter only affects when `EnMasking` is set.
  parameter int ReuseShare = 0
) (
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // KeyMgr sideload (secret key) interface
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // KeyMgr KDF data path
  input  keymgr_pkg::kmac_data_req_t keymgr_kdf_i,
  output keymgr_pkg::kmac_data_rsp_t keymgr_kdf_o,

  // TODO: CSRNG (EDN) interface

  // interrupts
  output logic intr_kmac_done_o,
  output logic intr_fifo_empty_o,
  output logic intr_kmac_err_o
);

  import kmac_reg_pkg::*;

  ////////////////
  // Parameters //
  ////////////////
  localparam int Share = (EnMasking) ? 2 : 1 ;

  /////////////////
  // Definitions //
  /////////////////

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
  logic sha3_start, sha3_run, sha3_done, sha3_absorbed;

  kmac_pkg::sha3_st_e sha3_fsm;

  // Prefix: kmac_pkg defines Prefix based on N size and S size.
  // Then computes left_encode(len(N)) size and left_encode(len(S))
  // For given default value 32, 256 bits, the max
  // encode_string(N) || encode_string(S) is 328. So 11 Prefix registers are
  // created.
  logic [kmac_pkg::NSRegisterSize*8-1:0] ns_prefix;

  // NumWordsPrefix from kmac_reg_pkg
  `ASSERT_INIT(PrefixRegSameToPrefixPkg_A,
               kmac_reg_pkg::NumWordsPrefix*4 == kmac_pkg::NSRegisterSize)

  // Output state: this is used to redirect the digest to KeyMgr or Software
  // depends on the configuration.
  logic state_valid;
  logic [kmac_pkg::StateW-1:0] state [Share];

  // SHA3 Entropy interface
  logic sha3_rand_valid, sha3_rand_consumed;
  logic [kmac_pkg::StateW-1:0] sha3_rand_data;
  // TODO: Connect to entropy when ready
  assign sha3_rand_valid = 1'b 1;
  assign sha3_rand_data = '0;

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
  logic [MaxKeyLen-1:0] key_data [Share];
  key_len_e             key_len;

  // KeyMgr interface control
  logic keymgr_en;

  // SHA3 Error response
  err_t sha3_err;

  //////////////////////////////////////
  // Connecting Register IF to logics //
  //////////////////////////////////////

  // Function-name N and Customization input string S
  always_comb begin
    for (int i = 0 ; i < NumWordsPrefix; i++) begin
      ns_prefix[32*i+:32] = reg2hw.prefix[NumWordsPrefix-1 - i].q;
    end
  end

  // Command signals
  // TODO: Make the entire logic to use enum rather than signal
  kmac_cmd_e cmd;
  assign cmd = kmac_cmd_e'(reg2hw.cmd.q);
  `ASSERT_KNOWN(KmacCmd_A, cmd)
  always_comb begin
    sha3_start = 1'b 0;
    sha3_run = 1'b 0;
    sha3_done = 1'b 0;
    reg2msgfifo_process = 1'b 0;
    if (reg2hw.cmd.qe) begin
      unique case (cmd)
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

        default: begin
          // TODO: Raise an error here
        end
      endcase
    end // if reg2hw.cmd.qe
  end

  // Status register ==========================================================
  // status.squeeze is valid only when SHA3 engine completes the Absorb and not
  // running the manual keccak rounds. This status is for SW to determine when
  // to read the STATE values.
  assign hw2reg.status.sha3_idle.d     = sha3_fsm == kmac_pkg::StIdle;
  assign hw2reg.status.sha3_absorb.d   = sha3_fsm == kmac_pkg::StAbsorb;
  assign hw2reg.status.sha3_squeeze.d  = sha3_fsm == kmac_pkg::StSqueeze;

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
  assign engine_stable = sha3_fsm == kmac_pkg::StIdle;

  assign hw2reg.cfg_regwen.d = engine_stable;

  // Secret Key
  // Secret key is defined as external register. So the logic latches when SW
  // writes to KEY_SHARE0 , KEY_SHARE1 registers.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      key_data[0] <= '0;
    end else if (engine_stable) begin
      for (int j = 0 ; j < MaxKeyLen/32 ; j++) begin
        if (reg2hw.key_share0[j].qe) begin
          key_data[0][32*j+:32] <= reg2hw.key_share0[j].q;
        end
      end // for j
    end // else if engine_stable
  end // always_ff

  if (EnMasking) begin : gen_key_masked
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        key_data[1] <= '0;
      end else if (engine_stable) begin
        for (int i = 0 ; i < MaxKeyLen/32 ; i++) begin
          if (reg2hw.key_share1[i].qe) begin
            key_data[1][32*i+:32] <= reg2hw.key_share1[i].q;
          end
        end // for i
      end // else if engine_stable
    end // always_ff
  end else begin : gen_unused_key_share1
    logic unused_keyshare1;
    assign unused_keyshare1 = ^reg2hw.key_share1;
  end

  assign key_len = key_len_e'(reg2hw.key_len.q);

  // TODO: Implement KeyMgr interface module. As of now, tying them to default value
  assign keymgr_kdf_o = '{
    ready: 1'b 0,
    digest_share0: '0,
    digest_share1: '0,
    done: 1'b 0,
    error: 1'b 0
  };

  ///////////////
  // Interrupt //
  ///////////////

  logic event_msgfifo_empty, msgfifo_empty_q;

  // Hash process absorbed interrupt
  prim_intr_hw #(.Width(1)) intr_kmac_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (sha3_absorbed),
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
  assign event_error =  sha3_err.valid;

  // Assing error code to the register
  assign hw2reg.err_code.de = sha3_err.valid;
  assign hw2reg.err_code.d = {sha3_err.code , sha3_err.info};

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
    .mode_i     (sha3_mode_e'(reg2hw.cfg.mode.q)),
    .strength_i (keccak_strength_e'(reg2hw.cfg.kstrength.q)),

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
  sha3core #(
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
    .mode_i     (sha3_mode_e'(reg2hw.cfg.mode.q)),
    .strength_i (keccak_strength_e'(reg2hw.cfg.kstrength.q)),

    // Controls (CMD register)
    .start_i    (sha3_start       ),
    .process_i  (kmac2sha3_process),
    .run_i      (sha3_run         ),
    .done_i     (sha3_done        ),

    .absorbed_o (sha3_absorbed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o (state_valid),
    .state_o       (state), // [Share]

    .error_o (sha3_err)
  );

  // Message FIFO
  kmac_msgfifo #(
    .InWidth (32),
    .InDepth (512), // Shall be matched to the reg window size
    .OutWidth (kmac_pkg::MsgWidth),
    .MsgDepth (kmac_pkg::MsgFifoDepth)
  ) u_msgfifo (
    .clk_i,
    .rst_ni,

    .tl_i (tl_win_h2d[WinMsgFifo]),
    .tl_o (tl_win_d2h[WinMsgFifo]),

    .msg_valid_o (msgfifo_valid),
    .msg_data_o  (msgfifo_data[0]),
    .msg_strb_o  (msgfifo_strb),
    .msg_ready_i (msgfifo_ready),

    .fifo_empty_o (msgfifo_empty), // intr and status
    .fifo_full_o  (msgfifo_full),  // connected to status only
    .fifo_depth_o (msgfifo_depth),

    .endian_swap_i (reg2hw.cfg.msg_endianness.q),

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

    .valid_i (state_valid),
    .state_i (state),

    .endian_swap_i (reg2hw.cfg.state_endianness.q)
  );

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

