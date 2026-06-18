// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Controller for life cycle / key management / RMA handling
//

module rram_ctrl_lcmgr
  import rram_ctrl_pkg::*;
  import lc_ctrl_pkg::lc_tx_t;
  import rram_ctrl_reg_pkg::rram_ctrl_reg2hw_control_reg_t;
#(
  parameter rram_key_t  RndCnstAddrKey  = RndCnstAddrKeyDefault,
  parameter rram_key_t  RndCnstDataKey  = RndCnstDataKeyDefault,
  parameter all_seeds_t RndCnstAllSeeds = RndCnstAllSeedsDefault,
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault
) (
  input logic clk_i,
  input logic rst_ni,
  input logic clk_otp_i,
  input logic rst_otp_ni,

  // only access seeds when provisioned
  input lc_tx_t lc_seed_hw_rd_en_i,

  // initialization command
  input logic lcmgr_init_i,

  // combined escalation disable
  input prim_mubi_pkg::mubi4_t disable_i,

  // interface to ctrl arb control ports
  output rram_ctrl_reg2hw_control_reg_t ctrl_o,
  output logic                          req_o,
  output logic [BusAddrByteW-1:0]       addr_o,
  input  logic                          done_i,
  input  rram_ctrl_err_t                err_i,
  output rram_phase_e                   phase_o,

  // interface to rram_ctrl_rd
  output logic                    rready_o,
  input  logic                    rvalid_i,
  input  logic [BusFullWidth-1:0] rdata_i,

  // interface to arbiter
  output logic                    wvalid_o,
  input  logic                    wready_i,
  output logic [BusFullWidth-1:0] wdata_o,

  // external rma request
  input  lc_tx_t                        rma_req_i,
  input  lc_ctrl_pkg::lc_nvm_rma_seed_t rma_seed_i,
  output lc_tx_t                        rma_ack_o,

  // seeds to the outside world,
  output logic [NumSeeds-1:0][SeedWidth-1:0] seeds_o,

  // fatal errors
  output logic fatal_err_o,
  output logic intg_err_o,

  // error status to registers
  output logic seed_err_o,

  // request otp keys
  output otp_ctrl_pkg::nvm_otp_key_req_t otp_key_req_o,
  input  otp_ctrl_pkg::nvm_otp_key_rsp_t otp_key_rsp_i,
  // scrambling keys
  output rram_key_t addr_key_o,
  output rram_key_t data_key_o,
  output rram_key_t rand_addr_key_o,
  output rram_key_t rand_data_key_o,

  // disable access to RRAM
  output lc_tx_t rma_dis_access_o,

  // scrambling keys have been read
  output logic keys_valid_o,
  // init has completed
  output logic init_done_o
);

  import lc_ctrl_pkg::lc_tx_test_true_strict;
  import lc_ctrl_pkg::lc_tx_and_hi;

  // total number of pages to be wiped during RMA entry
  localparam int unsigned WipeIdxWidth = prim_util_pkg::vbits(WipeEntries);
  localparam int unsigned MaxWipeEntry = WipeEntries - 1;

  // seed related local params
  localparam int unsigned SeedReads    = SeedWidth / BusWidth;
  localparam int unsigned SeedRdsWidth = $clog2(SeedReads);
  localparam int unsigned SeedCntWidth = $clog2(NumSeeds+1);
  localparam int unsigned NumSeedWidth = $clog2(NumSeeds);

  // the various seed outputs
  logic [NumSeeds-1:0][SeedReads-1:0][BusWidth-1:0] seeds_q;

  // lfsr for local entropy usage
  logic [31:0] rand_val;
  logic        lfsr_en;
  logic        lfsr_seed_en;

  // status bits
  logic keys_valid_q, keys_valid_d;
  logic init_done_q, init_done_d;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 11 -n 11 \
  //     -s 9473495713 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||| (38.18%)
  //  6: |||||||||||||||||||| (41.82%)
  //  7: |||||| (12.73%)
  //  8:  (1.82%)
  //  9: | (3.64%)
  // 10:  (1.82%)
  // 11: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 10
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 11;
  typedef enum logic [StateWidth-1:0] {
    StIdle          = 11'b00110001111,
    StReqAddrKey    = 11'b10111010000,
    StReqDataKey    = 11'b11001110110,
    StReadSeeds     = 11'b01011100001,
    StReadEval      = 11'b11100001001,
    StWait          = 11'b00000011000,
    StEntropyReseed = 11'b10010101010,
    StRmaWipe       = 11'b10011111101,
    StRmaRsp        = 11'b11010010011,
    StDisabled      = 11'b01100110101,
    StInvalid       = 11'b01101000010
  } lcmgr_state_e;

  lcmgr_state_e state_q, state_d;
  logic state_err;

  // SEC_CM: CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, lcmgr_state_e, StIdle)

  lc_tx_t                  err_sts_d, err_sts_q;
  logic                    err_sts_set;
  lc_tx_t                  rma_ack_d, rma_ack_q;
  logic                    validate_q, validate_d;
  logic [SeedCntWidth-1:0] seed_cnt_q;
  logic [SeedRdsWidth-1:0] addr_cnt_q;
  logic                    seed_cnt_en, seed_cnt_clr;
  logic                    addr_cnt_en, addr_cnt_clr;

  // RMA signals
  logic                    rma_wipe_req_d, rma_wipe_req_q, rma_wipe_done;
  logic [WipeIdxWidth-1:0] rma_wipe_idx;
  logic                    rma_wipe_idx_incr;
  rram_phase_e             phase;
  logic                    seed_phase;
  logic                    rma_phase;
  logic                    seed_err_q, seed_err_d;

  assign seed_phase = (phase == PhaseSeed);
  assign rma_phase  = (phase == PhaseRma);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rma_ack_q    <= lc_ctrl_pkg::Off;
      validate_q   <= 1'b0;
      seed_err_q   <= '0;
      keys_valid_q <= '0;
      init_done_q  <= '0;
    end else begin
      rma_ack_q    <= rma_ack_d;
      validate_q   <= validate_d;
      seed_err_q   <= seed_err_d;
      keys_valid_q <= keys_valid_d;
      init_done_q  <= init_done_d;
    end
  end

  assign seed_err_o = seed_err_q | seed_err_d;

  /////////////////////////
  // LC synchronization  //
  /////////////////////////
  lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en;
  logic provision_en;

  prim_lc_sync #(
    .NumCopies(1)
  ) u_lc_seed_hw_rd_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_seed_hw_rd_en_i),
    .lc_en_o({lc_seed_hw_rd_en})
  );

  assign provision_en = lc_tx_test_true_strict(lc_seed_hw_rd_en);

  ////////////////////
  // seed counters  //
  ////////////////////
  // SEC_CM: CTR.REDUN
  logic seed_cnt_err_d, seed_cnt_err_q;
  prim_count #(
    .Width(SeedCntWidth),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr)
  ) u_seed_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (seed_cnt_clr),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (seed_cnt_en),
    .decr_en_i         (1'b0),
    .step_i            (SeedCntWidth'(1'b1)),
    .commit_i          (1'b1),
    .cnt_o             (seed_cnt_q),
    .cnt_after_commit_o(),
    .err_o             (seed_cnt_err_d)
  );

  // SEC_CM: CTR.REDUN
  logic addr_cnt_err_d, addr_cnt_err_q;
  prim_count #(
    .Width(SeedRdsWidth),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr)
  ) u_addr_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (addr_cnt_clr),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (addr_cnt_en),
    .decr_en_i         (1'b0),
    .step_i            (SeedRdsWidth'(1'b1)),
    .commit_i          (1'b1),
    .cnt_o             (addr_cnt_q),
    .cnt_after_commit_o(),
    .err_o             (addr_cnt_err_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_err_q <= '0;
      seed_cnt_err_q <= '0;
    end else begin
      addr_cnt_err_q <= addr_cnt_err_q | addr_cnt_err_d;
      seed_cnt_err_q <= seed_cnt_err_q | seed_cnt_err_d;
    end
  end

  ///////////////////////////////
  // read data integrity check //
  ///////////////////////////////
  logic data_invalid_d, data_invalid_q;
  logic data_err;
  tlul_data_integ_dec u_data_intg_chk (
    .data_intg_i(rdata_i),
    .data_err_o (data_err)
  );

  // hold on to failed integrity until reset
  assign data_invalid_d = data_invalid_q | (rvalid_i & data_err);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_invalid_q <= '0;
    end else begin
      data_invalid_q <= data_invalid_d;
    end
  end

  ///////////////////////////////
  // store seed values in FFs  //
  ///////////////////////////////
  logic [SeedRdsWidth-1:0] rd_idx;
  logic [NumSeedWidth-1:0] seed_idx;

  assign rd_idx   = addr_cnt_q[SeedRdsWidth-1:0];
  assign seed_idx = seed_cnt_q[NumSeedWidth-1:0];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      seeds_q <= RndCnstAllSeeds;
    end else if (seed_phase && validate_q && rvalid_i) begin
      // validate current value
      seeds_q[seed_idx][rd_idx] <= seeds_q[seed_idx][rd_idx] &
                                   rdata_i[BusWidth-1:0];
    end else if (seed_phase && rvalid_i) begin
      seeds_q[seed_idx][rd_idx] <= rdata_i[BusWidth-1:0];
    end
  end

  logic [BusAddrW-1:0] seed_page_addr;

  assign seed_page_addr = BusAddrW'({SeedInfoPageSel[seed_idx], BusWordW'(0)});

  logic                start;
  rram_op_e            op;
  rram_part_e          part_sel;
  logic [9:0]          num_words;
  logic [BusAddrW-1:0] addr;

  // seed phase only reads from RRAM
  assign op = RramOpRead;

  typedef enum logic [1:0] {
    RmaReqInit,
    RmaReqKey,
    RmaReqWait,
    RmaReqLast
  } rma_req_idx_e;

  lc_tx_t [RmaReqLast-1:0] rma_req;
  prim_lc_sync #(
    .NumCopies(int'(RmaReqLast))
  ) u_sync_rma_req (
    .clk_i,
    .rst_ni,
    .lc_en_i(rma_req_i),
    .lc_en_o(rma_req)
  );

  ///////////////////////////////
  // OTP key requests          //
  ///////////////////////////////
  logic addr_key_req_d;
  logic addr_key_ack_q;
  logic data_key_req_d;
  logic data_key_ack_q;

  // req/ack to otp
  prim_sync_reqack u_addr_sync_reqack (
    .clk_src_i (clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i (clk_otp_i),
    .rst_dst_ni(rst_otp_ni),
    .req_chk_i (1'b1),
    .src_req_i (addr_key_req_d),
    .src_ack_o (addr_key_ack_q),
    .dst_req_o (otp_key_req_o.addr_req),
    .dst_ack_i (otp_key_rsp_i.addr_ack)
  );

  // req/ack to otp
  prim_sync_reqack u_data_sync_reqack (
    .clk_src_i (clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i (clk_otp_i),
    .rst_dst_ni(rst_otp_ni),
    .req_chk_i (1'b1),
    .src_req_i (data_key_req_d),
    .src_ack_o (data_key_ack_q),
    .dst_req_o (otp_key_req_o.data_req),
    .dst_ack_i (otp_key_rsp_i.data_ack)
  );

  // capture addr/data keys when valid is synchronized from otp_clk to clk
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_key_o <= RndCnstAddrKey;
      data_key_o <= RndCnstDataKey;
    end else begin
      if (addr_key_req_d && addr_key_ack_q) begin
        addr_key_o      <= rram_key_t'(otp_key_rsp_i.key);
        rand_addr_key_o <= rram_key_t'(otp_key_rsp_i.rand_key);
      end

      if (data_key_req_d && data_key_ack_q) begin
        data_key_o      <= rram_key_t'(otp_key_rsp_i.key);
        rand_data_key_o <= rram_key_t'(otp_key_rsp_i.rand_key);
      end
    end
  end

  ///////////////////////////////
  // Init state machine        //
  ///////////////////////////////
  logic rma_done;
  assign rma_done = lc_tx_test_true_strict(lc_tx_and_hi(rma_req[RmaReqInit], rma_ack_d));

  always_comb begin

    // phases of the hardware interface
    phase = PhaseNone;

    // timer controls
    seed_cnt_en  = 1'b0;
    seed_cnt_clr = 1'b0;
    addr_cnt_en  = 1'b0;
    addr_cnt_clr = 1'b0;

    // rram ctrl arb controls
    start     = 1'b0;
    addr      = '0;
    part_sel  = RramPartInfo;
    num_words = SeedReads - 12'd1;

    // seed status
    seed_err_d = seed_err_q;

    state_d    = state_q;
    rma_ack_d  = lc_ctrl_pkg::Off;
    validate_d = validate_q;

    addr_key_req_d = 1'b0;
    data_key_req_d = 1'b0;

    init_done_d  = init_done_q;
    keys_valid_d = keys_valid_q;

    // entropy handling
    lfsr_seed_en = 1'b0;
    lfsr_en      = 1'b0;

    // rma related
    rma_wipe_req_d    = rma_wipe_req_q;
    rma_wipe_idx_incr = 1'b0;

    // disable RRAM access entirely
    rma_dis_access_o = lc_ctrl_pkg::Off;

    state_err = 1'b0;

    unique case (state_q)

      // If rma request is seen, directly transition to wipe.
      // Since init has not been called, there are no guarantees
      // to entropy behavior, thus do not reseed
      StIdle: begin
        if (lc_tx_test_true_strict(rma_req[RmaReqInit])) begin
          state_d = StRmaWipe;
        end else if (lcmgr_init_i) begin
          state_d = StReqAddrKey;
        end
      end

      StReqAddrKey: begin
        addr_key_req_d = 1'b1;
        if (lc_tx_test_true_strict(rma_req[RmaReqKey])) begin
          state_d = StRmaWipe;
        end else if (addr_key_ack_q) begin
          state_d = StReqDataKey;
        end
      end

      StReqDataKey: begin
        data_key_req_d = 1'b1;
        if (lc_tx_test_true_strict(rma_req[RmaReqKey])) begin
          state_d = StRmaWipe;
        end else if (data_key_ack_q) begin
          // provision_en is only a "good" value after otp/lc initialization
          state_d      = provision_en ? StReadSeeds : StWait;
          keys_valid_d = 1'b1;
        end
      end

      // read seeds
      StReadSeeds: begin
        // seeds can be updated in this state
        phase = PhaseSeed;

        // kick off RRAM transaction
        start = 1'b1;
        addr = BusAddrW'(seed_page_addr);

        // we have checked all seeds, proceed
        addr_cnt_en = rvalid_i;
        if (seed_cnt_q == NumSeeds) begin
          start   = 1'b0;
          state_d = StWait;
        end else if (done_i) begin
          seed_err_d = |err_i;
          state_d    = StReadEval;
        end
      end // case: StReadSeeds

      StReadEval: begin
        phase        = PhaseSeed;
        addr_cnt_clr = 1'b1;
        state_d      = StReadSeeds;

        if (validate_q) begin
          seed_cnt_en = 1'b1;
          validate_d  = 1'b0;
        end else begin
          validate_d = 1'b1;
        end
      end

      // Waiting for an rma entry command
      StWait: begin
        init_done_d = 1'b1;
        if (lc_tx_test_true_strict(rma_req[RmaReqWait])) begin
          state_d = StEntropyReseed;
        end
      end

      // Reseed entropy
      StEntropyReseed: begin
        lfsr_seed_en = 1'b1;
        state_d      = StRmaWipe;
      end

      StRmaWipe: begin
        phase          = PhaseRma;
        lfsr_en        = 1'b1;
        rma_wipe_req_d = 1'b1;

        if (rma_wipe_idx == MaxWipeEntry[WipeIdxWidth-1:0] && rma_wipe_done) begin
          // first check for error status
          // If error status is set, go directly to invalid terminal state
          // If error status is good, go to second check
          state_d        = lc_ctrl_pkg::lc_tx_test_false_loose(err_sts_q) ? StInvalid : StRmaRsp;
          rma_wipe_req_d = 1'b0;
        end else if (rma_wipe_done) begin
          rma_wipe_idx_incr = 1;
        end
      end

      // response to rma request
      // Second check for error status:
      // If error status indicates error, jump to invalid terminal state
      // Otherwise assign output to error status;
      StRmaRsp: begin
        phase            = PhaseRma;
        rma_dis_access_o = lc_ctrl_pkg::On;
        if (lc_ctrl_pkg::lc_tx_test_false_loose(err_sts_q)) begin
          state_d = StInvalid;
        end else begin
          rma_ack_d = err_sts_q;
        end
      end

      // Disabled state is functionally equivalent to invalid, just without the
      // the explicit error-ing
      StDisabled: begin
        rma_dis_access_o = lc_ctrl_pkg::On;
        rma_ack_d        = lc_ctrl_pkg::Off;
        state_d          = StDisabled;
      end

      StInvalid: begin
        rma_dis_access_o = lc_ctrl_pkg::On;
        state_err        = 1'b1;
        rma_ack_d        = lc_ctrl_pkg::Off;
        state_d          = StInvalid;
      end

      // Invalid catch-all state
      default: begin
        rma_dis_access_o = lc_ctrl_pkg::On;
        state_err        = 1'b1;
        keys_valid_d     = 1'b0;
        state_d          = StInvalid;
      end

    endcase // unique case (state_q)

    // This fsm does not directly interface with RRAM and can be
    // be transitioned to invalid immediately.
    // If rma transition is successful however, do not transition
    // and continue acking the life cycle controller, as disable is
    // expected behavior under this situation.
    if (prim_mubi_pkg::mubi4_test_true_loose(disable_i) &&
        state_d != StInvalid &&
        !rma_done) begin
      state_d = StDisabled;
      keys_valid_d     = 1'b0;
    end

  end // always_comb

  // If state is already invalid, disable has no impact.
  // If state is currently in StRmaRsp with a successful RMA transition, also do not
  // transition to disabled state as we need to continue acknowledging lc_ctrl.
  `ASSERT(DisableChk_A, prim_mubi_pkg::mubi4_test_true_loose(disable_i) & state_q != StRmaRsp
          |=> state_q == StDisabled)


  ///////////////////////////////
  // RMA wiping Mechanism      //
  ///////////////////////////////
  localparam int unsigned PageCntWidth = prim_util_pkg::vbits(TotalPages + 1);
  localparam int unsigned WordCntWidth = prim_util_pkg::vbits(BusWordsPerPage + 1);

  logic                    page_cnt_ld;
  logic                    page_cnt_incr;
  logic                    page_cnt_clr;
  logic                    word_cnt_incr;
  logic                    word_cnt_clr;
  logic                    wr_cnt_en;
  logic                    rd_cnt_en;
  logic [PageCntWidth-1:0] page_cnt, end_page;
  logic [WordCntWidth-1:0] word_cnt;
  logic [BusWidth-1:0]     wr_data_xor_q, wr_data_xor_d;
  logic [BusWidth-1:0]     rd_data_xor_q, rd_data_xor_d;

  assign end_page = RmaWipeEntries[rma_wipe_idx].base +
                    RmaWipeEntries[rma_wipe_idx].size;

  // RMA control FSM encoding
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 8 -n 10 \
  //     -s 1231234544 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (50.00%)
  //  6: ||||||||||||||| (39.29%)
  //  7: || (7.14%)
  //  8: | (3.57%)
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 9
  //
  localparam int RmaStateWidth = 10;
  typedef enum logic [RmaStateWidth-1:0] {
    StRmaIdle      = 10'b1011111111,
    StRmaPageSel   = 10'b0000100100,
    StRmaWrite     = 10'b1101101001,
    StRmaWriteWait = 10'b0100011110,
    StRmaRdVerify  = 10'b1110010011,
    StRmaRdCheck   = 10'b0001010001,
    StRmaDisabled  = 10'b1111000100,
    StRmaInvalid   = 10'b0011001010
  } rma_state_e;
  rma_state_e rma_state_d, rma_state_q;

  // SEC_CM: CTRL.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_rma_state_regs, rma_state_d, rma_state_q, rma_state_e, StRmaIdle)

  // SEC_CM: CTR.REDUN
  logic page_err_q, page_err_d;
  prim_count #(
    .Width(PageCntWidth),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr|
                     prim_count_pkg::Set)
  ) u_page_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (page_cnt_clr),
    .set_i             (page_cnt_ld),
    .set_cnt_i         (PageCntWidth'(RmaWipeEntries[rma_wipe_idx].base)),
    .incr_en_i         (page_cnt_incr),
    .decr_en_i         (1'b0),
    .step_i            (PageCntWidth'(1)),
    .commit_i          (1'b1),
    .cnt_o             (page_cnt),
    .cnt_after_commit_o(),
    .err_o             (page_err_d)
  );

  logic word_err_q, word_err_d;
  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(WordCntWidth),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Incr)
  ) u_word_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             (word_cnt_clr),
    .set_i             (1'b0),
    .set_cnt_i         ('0),
    .incr_en_i         (word_cnt_incr),
    .decr_en_i         (1'b0),
    .step_i            (WordCntWidth'(1)),
    .commit_i          (1'b1),
    .cnt_o             (word_cnt),
    .cnt_after_commit_o(),
    .err_o             (word_err_d)
  );

  logic rma_idx_err_q, rma_idx_err_d;
  // SEC_CM: CTR.REDUN
  prim_count #(
    .Width(WipeIdxWidth),
    .PossibleActions({prim_count_pkg::Incr})
  ) u_wipe_idx_cnt (
    .clk_i,
    .rst_ni,
    .clr_i             ('0),
    .set_i             ('0),
    .set_cnt_i         ('0),
    .incr_en_i         (rma_wipe_idx_incr),
    .decr_en_i         (1'b0),
    .step_i            (WipeIdxWidth'(1'b1)),
    .commit_i          (1'b1),
    .cnt_o             (rma_wipe_idx),
    .cnt_after_commit_o(),
    .err_o             (rma_idx_err_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      page_err_q     <= '0;
      word_err_q     <= '0;
      rma_idx_err_q  <= '0;
      rma_wipe_req_q <= '0;
    end else begin
      page_err_q     <= page_err_q | page_err_d;
      word_err_q     <= word_err_q | word_err_d;
      rma_idx_err_q  <= rma_idx_err_q | rma_idx_err_d;
      rma_wipe_req_q <= rma_wipe_req_d;
    end
  end

  // create weak digest of written and read data
  always_comb begin
    wr_data_xor_d = wr_data_xor_q;
    rd_data_xor_d = rd_data_xor_q;
    if (wr_cnt_en && wvalid_o && wready_i) begin
      if (word_cnt == '0) begin
        wr_data_xor_d = rand_val;
      end else begin
        wr_data_xor_d = wr_data_xor_q ^ rand_val;
      end
    end
    if (rd_cnt_en && rvalid_i && rready_o) begin
      if (word_cnt == '0) begin
        rd_data_xor_d = rdata_i[BusWidth-1:0];
      end else begin
        rd_data_xor_d = rd_data_xor_q ^ rdata_i[BusWidth-1:0];
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr_data_xor_q <= '0;
      rd_data_xor_q <= '0;
    end else begin
      wr_data_xor_q <= wr_data_xor_d;
      rd_data_xor_q <= rd_data_xor_d;
    end
  end

  // once error is set to off, it cannot be unset without a reboot
  // On - no errors
  // Off - errors were observed
  logic [lc_ctrl_pkg::TxWidth-1:0] err_sts_raw_q;

  assign err_sts_q = lc_tx_t'(err_sts_raw_q);
  assign err_sts_d = err_sts_set && lc_ctrl_pkg::lc_tx_test_true_loose(err_sts_q) ?
                     lc_ctrl_pkg::Off : err_sts_q;
  // This primitive is used to place a size-only constraint on the flops in order to prevent
  // optimizations. Without this Vivado may infer combo loops. For details, see
  // https://github.com/lowRISC/opentitan/issues/10204
  prim_flop #(
    .Width(lc_ctrl_pkg::TxWidth),
    .ResetValue(lc_ctrl_pkg::TxWidth'(lc_ctrl_pkg::On))
  ) u_prim_flop_err_sts (
    .clk_i,
    .rst_ni,
    .d_i(err_sts_d),
    .q_o(err_sts_raw_q)
  );

  logic                rma_start;
  logic [BusAddrW-1:0] rma_addr;
  rram_op_e            rma_op;
  rram_part_e          rma_part_sel;
  logic [9:0]          rma_num_words;

  assign rma_addr = BusAddrW'({page_cnt[PageW-1:0], BusWordW'(0)});

  assign rma_part_sel  = RmaWipeEntries[rma_wipe_idx].part;
  assign rma_num_words = BusWordsPerPage - 1;
  //fsm for handling the actual wipe
  logic fsm_err;

  // SEC_CM: RMA_ENTRY.MEM.SEC_WIPE
  always_comb begin
    rma_state_d   = rma_state_q;
    rma_wipe_done = 1'b0;
    rma_start     = 1'b0;
    rma_op        = RramOpRead;
    err_sts_set   = 1'b0;
    page_cnt_ld   = 1'b0;
    page_cnt_incr = 1'b0;
    page_cnt_clr  = 1'b0;
    word_cnt_incr = 1'b0;
    word_cnt_clr  = 1'b0;
    wr_cnt_en     = 1'b0;
    rd_cnt_en     = 1'b0;
    fsm_err       = 1'b0;

    unique case (rma_state_q)
      // Transition to invalid state via disable only when any ongoing stateful
      // operations are complete. This ensures we do not electrically disturb
      // any ongoing operation.
      // This of course cannot be guaranteed if the FSM state is directly disturbed,
      // and that is considered an extremely invasive attack.
      StRmaIdle: begin
        if (prim_mubi_pkg::mubi4_test_true_loose(disable_i)) begin
          rma_state_d = StRmaDisabled;
        end else if (rma_wipe_req_q) begin
          rma_state_d = StRmaPageSel;
          page_cnt_ld = 1'b1;
        end
      end

      StRmaPageSel: begin
        if (prim_mubi_pkg::mubi4_test_true_loose(disable_i)) begin
          rma_state_d = StRmaDisabled;
        end else if (page_cnt <= end_page) begin
          rma_state_d = StRmaWrite;
        end else begin
          rma_wipe_done = 1'b1;
          page_cnt_clr = 1'b1;
          rma_state_d  = StRmaIdle;
        end
      end

      StRmaWrite: begin
        rma_start = 1'b1;
        rma_op    = RramOpWrite;

        if (wready_i) begin
          wr_cnt_en     = 1'b1;
          word_cnt_incr = 1'b1;
        end

        if ((word_cnt == BusWordsPerPage - 1) && wready_i) begin
          rma_state_d = StRmaWriteWait;
        end
      end

      StRmaWriteWait: begin
        rma_start = 1'b1;
        rma_op    = RramOpWrite;

        if (done_i) begin
          word_cnt_clr = 1'b1;
          err_sts_set  = |err_i;
          rma_state_d  = StRmaRdVerify;
        end
      end

      StRmaRdVerify: begin
        rma_start = 1'b1;
        rma_op    = RramOpRead;

        if(rvalid_i) begin
          rd_cnt_en     = 1'b1;
          word_cnt_incr = 1'b1;
        end

        if ((word_cnt == BusWordsPerPage - 1) && done_i) begin
          word_cnt_clr = 1'b1;
          err_sts_set  = |err_i;
          rma_state_d  = StRmaRdCheck;
        end
      end

      StRmaRdCheck: begin
        if (wr_data_xor_q != rd_data_xor_q) begin
          err_sts_set = 1'b1;
        end
        rma_state_d   = StRmaPageSel;
        page_cnt_incr = 1'b1;
      end

      StRmaDisabled: begin
        rma_state_d = StRmaDisabled;
      end

      StRmaInvalid: begin
        rma_state_d = StRmaInvalid;
        err_sts_set = 1'b1;
        fsm_err     = 1'b1;
      end

      default: begin
        rma_state_d = StRmaInvalid;
        fsm_err     = 1'b1;
      end

    endcase // unique case (rma_state_q)

  end // always_comb

  prim_lfsr #(
    .LfsrDw(LfsrWidth),
    .StateOutDw(LfsrWidth),
    .DefaultSeed(RndCnstLfsrSeed),
    .StatePermEn(1),
    .StatePerm(RndCnstLfsrPerm)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i(lfsr_seed_en),
    .seed_i   (rma_seed_i),
    .lfsr_en_i(lfsr_en),
    .entropy_i('0),
    .state_o  (rand_val)
  );

  tlul_data_integ_enc u_bus_intg (
    .data_i     (rand_val),
    .data_intg_o(wdata_o)
  );

  assign wvalid_o = wr_cnt_en;

  assign ctrl_o.start.q     = seed_phase ? start     : rma_start;
  assign ctrl_o.op.q        = seed_phase ? op        : rma_op;
  assign ctrl_o.partition.q = seed_phase ? part_sel  : rma_part_sel;
  assign ctrl_o.num.q       = seed_phase ? num_words : rma_num_words;
  // address is consistent with software width format (full bus)
  assign addr_o = seed_phase ? {addr, {BusByteWidth{1'b0}}} :
                               {rma_addr, {BusByteWidth{1'b0}}};

  assign req_o    = seed_phase | rma_phase;
  assign rready_o = 1'b1;
  assign seeds_o  = seeds_q;
  assign phase_o  = phase;

  assign rma_ack_o = rma_ack_q;

  assign keys_valid_o = keys_valid_q;
  assign init_done_o  = init_done_q;

  // all of these are considered fatal errors
  assign fatal_err_o = page_err_q | word_err_q | fsm_err | state_err | rma_idx_err_q |
                       addr_cnt_err_q | seed_cnt_err_q;

  // integrity error is its own category
  assign intg_err_o = data_invalid_q;

  logic unused_seed_valid;
  assign unused_seed_valid = otp_key_rsp_i.seed_valid;

endmodule // rram_ctrl_lcmgr
