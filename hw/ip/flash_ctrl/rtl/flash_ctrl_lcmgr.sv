// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller for life cycle / key management handling
//

module flash_ctrl_lcmgr import flash_ctrl_pkg::*; #(
  parameter flash_key_t RndCnstAddrKey = RndCnstAddrKeyDefault,
  parameter flash_key_t RndCnstDataKey = RndCnstDataKeyDefault
) (
  input clk_i,
  input rst_ni,
  input clk_otp_i,
  input rst_otp_ni,

  // initialization command
  input init_i,

  // only access seeds when provisioned
  input provision_en_i,

  // interface to ctrl arb control ports
  output flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t ctrl_o,
  output logic req_o,
  output logic [BusAddrByteW-1:0] addr_o,
  input done_i,
  input flash_ctrl_err_t err_i,

  // interface to ctrl_arb data ports
  output logic rready_o,
  input rvalid_i,
  output logic wvalid_o,
  input wready_i,

  // direct form rd_fifo
  input [BusWidth-1:0] rdata_i,

  // direct to wr_fifo
  output logic [BusWidth-1:0] wdata_o,

  // external rma request
  // This should be simplified to just multi-bit request and multi-bit response
  input lc_ctrl_pkg::lc_tx_t rma_req_i,
  output lc_ctrl_pkg::lc_tx_t rma_ack_o,

  // seeds to the outside world,
  output logic [NumSeeds-1:0][SeedWidth-1:0] seeds_o,

  // indicate to memory protection what phase the hw interface is in
  output flash_lcmgr_phase_e phase_o,

  // fatal errors
  output logic fatal_err_o,

  // error status to registers
  output logic seed_err_o,

  // enable read buffer in flash_phy
  output logic rd_buf_en_o,

  // request otp keys
  output otp_ctrl_pkg::flash_otp_key_req_t otp_key_req_o,
  input otp_ctrl_pkg::flash_otp_key_rsp_t otp_key_rsp_i,
  output flash_key_t addr_key_o,
  output flash_key_t data_key_o,
  output flash_key_t rand_addr_key_o,
  output flash_key_t rand_data_key_o,

  // entropy interface
  output logic edn_req_o,
  input edn_ack_i,
  output logic lfsr_en_o,
  input [BusWidth-1:0] rand_i,

  // disable access to flash
  output lc_ctrl_pkg::lc_tx_t dis_access_o,

  // init ongoing
  output logic init_busy_o
);

  // total number of pages to be wiped during RMA entry
  localparam int unsigned WipeIdxWidth = prim_util_pkg::vbits(WipeEntries);
  localparam int unsigned MaxWipeEntry = WipeEntries - 1;

  // seed related local params
  localparam int unsigned SeedReads = SeedWidth / BusWidth;
  localparam int unsigned SeedRdsWidth = $clog2(SeedReads);
  localparam int unsigned SeedCntWidth = $clog2(NumSeeds+1);
  localparam int unsigned NumSeedWidth = $clog2(NumSeeds);

  // the various seed outputs
  logic [NumSeeds-1:0][SeedReads-1:0][BusWidth-1:0] seeds_q;

  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (40.00%)
  //  6: |||||||||||||||| (33.33%)
  //  7: ||||| (11.11%)
  //  8: |||||| (13.33%)
  //  9: | (2.22%)
  // 10: --
  // 11: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 9
  // Minimum Hamming weight: 4
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 11;
  typedef enum logic [StateWidth-1:0] {
    StIdle          = 11'b01010101111,
    StReqAddrKey    = 11'b01001110011,
    StReqDataKey    = 11'b11010000100,
    StReadSeeds     = 11'b10001010101,
    StReadEval      = 11'b11110110010,
    StWait          = 11'b00111101010,
    StEntropyReseed = 11'b11101001000,
    StRmaWipe       = 11'b00010011001,
    StRmaRsp        = 11'b10100100001,
    StInvalid       = 11'b10100011110
  } lcmgr_state_e;

  lcmgr_state_e state_q, state_d;
  logic state_err;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = lcmgr_state_e'(state_raw_q);
  //SEC_CM: FSM.SPARSE
  prim_sparse_fsm_flop #(
    .StateEnumT(lcmgr_state_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(StIdle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( state_d ),
    .state_o ( state_raw_q )
  );

  lc_ctrl_pkg::lc_tx_t err_sts_d, err_sts_q;
  logic err_sts_set;
  lc_ctrl_pkg::lc_tx_t rma_ack_d, rma_ack_q;
  logic validate_q, validate_d;
  logic [SeedCntWidth-1:0] seed_cnt_q;
  logic [SeedRdsWidth-1:0] addr_cnt_q;
  logic seed_cnt_en, seed_cnt_clr;
  logic addr_cnt_en, addr_cnt_clr;
  logic rma_wipe_req, rma_wipe_done, rma_wipe_req_int;
  logic [WipeIdxWidth-1:0] rma_wipe_idx;
  logic rma_wipe_idx_incr;
  flash_lcmgr_phase_e phase;
  logic seed_phase;
  logic rma_phase;
  logic seed_err_q, seed_err_d;

  assign seed_phase = phase == PhaseSeed;
  assign rma_phase = phase == PhaseRma;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rma_ack_q <= lc_ctrl_pkg::Off;
      validate_q <= 1'b0;
      seed_err_q <= '0;
    end else begin
      rma_ack_q <= rma_ack_d;
      validate_q <= validate_d;
      seed_err_q <= seed_err_d;
    end
  end

  assign seed_err_o = seed_err_q;

  // seed cnt tracks which seed round we are handling at the moment
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      seed_cnt_q <= '0;
    end else if (seed_cnt_clr) begin
      seed_cnt_q <= '0;
    end else if (seed_cnt_en) begin
      seed_cnt_q <= seed_cnt_q + 1'b1;
    end
  end

  // addr cnt tracks how far we are in an address looop
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_q <= '0;
    end else if (addr_cnt_clr) begin
      addr_cnt_q <= '0;
    end else if (addr_cnt_en) begin
      addr_cnt_q <= addr_cnt_q + 1'b1;
    end
  end

  // capture the seed values
  logic [SeedRdsWidth-1:0] rd_idx;
  logic [NumSeedWidth-1:0] seed_idx;
  assign rd_idx = addr_cnt_q[SeedRdsWidth-1:0];
  assign seed_idx = seed_cnt_q[NumSeedWidth-1:0];
  always_ff @(posedge clk_i) begin
    // validate current value
    if (seed_phase && validate_q && rvalid_i) begin
      seeds_q[seed_idx][rd_idx] <= seeds_q[seed_idx][rd_idx] &
                                   rdata_i;
    end else if (seed_phase && rvalid_i) begin
      seeds_q[seed_idx][rd_idx] <= rdata_i;
    end
  end

  page_addr_t seed_page;
  logic [InfoTypesWidth-1:0] seed_info_sel;
  logic [BusAddrW-1:0] seed_page_addr;
  assign seed_page = SeedInfoPageSel[seed_idx];
  assign seed_info_sel = seed_page.sel;
  assign seed_page_addr = BusAddrW'({seed_page.addr, BusWordW'(0)});

  logic start;
  flash_op_e op;
  flash_prog_e prog_type;
  flash_erase_e erase_type;
  flash_part_e part_sel;
  logic [InfoTypesWidth-1:0] info_sel;
  logic [11:0] num_words;
  logic [BusAddrW-1:0] addr;

  assign prog_type = FlashProgNormal;
  assign erase_type = FlashErasePage;
  // seed phase is always read
  // rma phase is erase unless we are validating
  assign op = FlashOpRead;

  // synchronize inputs
  logic init_q;

  prim_flop_2sync #(
    .Width(1),
    .ResetValue(0)
  ) u_sync_flash_init (
    .clk_i,
    .rst_ni,
    .d_i(init_i),
    .q_o(init_q)
  );

  typedef enum logic [1:0] {
    RmaReqInit,
    RmaReqKey,
    RmaReqWait,
    RmaReqLast
  } rma_req_idx_e;

  lc_ctrl_pkg::lc_tx_t [RmaReqLast-1:0] rma_req;
  prim_lc_sync #(
    .NumCopies(int'(RmaReqLast))
  ) u_sync_rma_req (
    .clk_i,
    .rst_ni,
    .lc_en_i(rma_req_i),
    .lc_en_o(rma_req)
  );

  logic addr_key_req_d;
  logic addr_key_ack_q;
  logic data_key_req_d;
  logic data_key_ack_q;

  // req/ack to otp
  prim_sync_reqack u_addr_sync_reqack (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i(clk_otp_i),
    .rst_dst_ni(rst_otp_ni),
    .req_chk_i(1'b1),
    .src_req_i(addr_key_req_d),
    .src_ack_o(addr_key_ack_q),
    .dst_req_o(otp_key_req_o.addr_req),
    .dst_ack_i(otp_key_rsp_i.addr_ack)
  );

  // req/ack to otp
  prim_sync_reqack u_data_sync_reqack (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .clk_dst_i(clk_otp_i),
    .rst_dst_ni(rst_otp_ni),
    .req_chk_i(1'b1),
    .src_req_i(data_key_req_d),
    .src_ack_o(data_key_ack_q),
    .dst_req_o(otp_key_req_o.data_req),
    .dst_ack_i(otp_key_rsp_i.data_ack)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_key_o <= RndCnstAddrKey;
      data_key_o <= RndCnstDataKey;
    end else begin
      if (addr_key_req_d && addr_key_ack_q) begin
        addr_key_o <= flash_key_t'(otp_key_rsp_i.key);
        rand_addr_key_o <= flash_key_t'(otp_key_rsp_i.rand_key);
      end

      if (data_key_req_d && data_key_ack_q) begin
        data_key_o <= flash_key_t'(otp_key_rsp_i.key);
        rand_data_key_o <= flash_key_t'(otp_key_rsp_i.rand_key);
      end
    end
  end


  ///////////////////////////////
  // Hardware Interface FSM
  ///////////////////////////////
  always_comb begin

    // phases of the hardware interface
    phase = PhaseNone;

    // timer controls
    seed_cnt_en = 1'b0;
    seed_cnt_clr = 1'b0;
    addr_cnt_en = 1'b0;
    addr_cnt_clr = 1'b0;

    // flash ctrrl arb controls
    start = 1'b0;
    addr = '0;
    part_sel = FlashPartInfo;
    info_sel = 0;
    num_words = SeedReads[11:0] - 12'd1;

    // seed status
    seed_err_d = seed_err_q;

    state_d = state_q;
    rma_ack_d = lc_ctrl_pkg::Off;
    validate_d = validate_q;

    // read buffer enable
    rd_buf_en_o = 1'b0;

    addr_key_req_d = 1'b0;
    data_key_req_d = 1'b0;

    // entropy handling
    edn_req_o = 1'b0;
    lfsr_en_o = 1'b0;

    // rma related
    rma_wipe_req = 1'b0;
    rma_wipe_idx_incr = 1'b0;

    // disable flash access entirely
    dis_access_o = lc_ctrl_pkg::Off;

    state_err = 1'b0;

    unique case (state_q)

      // If rma request is seen, directly transition to wipe.
      // Since init has not been called, there are no guarantees
      // to entropy behavior, thus do not reseed
      StIdle: begin
        if (rma_req[RmaReqInit] == lc_ctrl_pkg::On) begin
          state_d = StRmaWipe;
        end else if (init_q) begin
          state_d = StReqAddrKey;
        end
      end

      StReqAddrKey: begin
        phase = PhaseSeed;
        addr_key_req_d = 1'b1;
        if (rma_req[RmaReqKey] == lc_ctrl_pkg::On) begin
          state_d = StRmaWipe;
        end else if (addr_key_ack_q) begin
          state_d = StReqDataKey;
        end
      end

      StReqDataKey: begin
        phase = PhaseSeed;
        data_key_req_d = 1'b1;
        if (rma_req[RmaReqKey] == lc_ctrl_pkg::On) begin
          state_d = StRmaWipe;
        end else if (data_key_ack_q) begin
          // provision_en is only a "good" value after otp/lc initialization
          state_d = provision_en_i ? StReadSeeds : StWait;
        end
      end

      // read seeds
      StReadSeeds: begin
        // seeds can be updated in this state
        phase = PhaseSeed;

        // kick off flash transaction
        start = 1'b1;
        addr = BusAddrW'(seed_page_addr);
        info_sel = seed_info_sel;

        // we have checked all seeds, proceed
        addr_cnt_en = rvalid_i;
        if (seed_cnt_q == NumSeeds) begin
          start = 1'b0;
          state_d = StWait;
        end else if (done_i) begin
          seed_err_d = |err_i | seed_err_q;
          state_d = StReadEval;
        end
      end // case: StReadSeeds

     StReadEval: begin
         addr_cnt_clr = 1'b1;
         state_d = StReadSeeds;

         if (validate_q) begin
            seed_cnt_en = 1'b1;
            validate_d = 1'b0;
         end else begin
            validate_d = 1'b1;
         end
      end

      // Waiting for an rma entry command
      StWait: begin
        rd_buf_en_o = 1'b1;
        if (rma_req[RmaReqWait] == lc_ctrl_pkg::On) begin
          state_d = StEntropyReseed;
        end
      end

      // Reseed entropy
      StEntropyReseed: begin
        edn_req_o = 1'b1;
        if(edn_ack_i) begin
          state_d = StRmaWipe;
        end
      end

      StRmaWipe: begin
        phase = PhaseRma;
        lfsr_en_o = 1'b1;
        rma_wipe_req = 1'b1;

        if (rma_wipe_idx == MaxWipeEntry[WipeIdxWidth-1:0] && rma_wipe_done) begin
          // first check for error status
          // If error status is set, go directly to invalid terminal state
          // If error status is good, go to second check
          state_d = (err_sts_q != lc_ctrl_pkg::On) ? StInvalid : StRmaRsp;
        end else if (rma_wipe_done) begin
          rma_wipe_idx_incr = 1;
        end
      end

      // response to rma request
      // Second check for error status:
      // If error status indicates error, jump to invalid terminal state
      // Otherwise assign output to error status;
      StRmaRsp: begin
        phase = PhaseRma;
        dis_access_o = lc_ctrl_pkg::On;
        if (err_sts_q != lc_ctrl_pkg::On) begin
          state_d = StInvalid;
        end else begin
          rma_ack_d = err_sts_q;
        end
      end

      StInvalid: begin
        dis_access_o = lc_ctrl_pkg::On;
        state_err = 1'b1;
        // Setting PhaseInvalid causes Vivado to erroneously infer combo loops. For details, see
        // https://github.com/lowRISC/opentitan/issues/10204
        //phase = PhaseInvalid;
        rma_ack_d = lc_ctrl_pkg::Off;
      end

      // Invalid catch-all state
      default: begin
        dis_access_o = lc_ctrl_pkg::On;
        state_d = StInvalid;
      end

    endcase // unique case (state_q)
  end // always_comb

  ///////////////////////////////
  // RMA wiping Mechanism
  ///////////////////////////////

  localparam int unsigned PageCntWidth = prim_util_pkg::vbits(PagesPerBank + 1);
  localparam int unsigned WordCntWidth = prim_util_pkg::vbits(BusWordsPerPage + 1);
  localparam int unsigned BeatCntWidth = prim_util_pkg::vbits(WidthMultiple);
  localparam int unsigned MaxBeatCnt = WidthMultiple - 1;

  logic page_cnt_ld;
  logic page_cnt_incr;
  logic page_cnt_clr;
  logic word_cnt_incr;
  logic word_cnt_ld;
  logic word_cnt_clr;
  logic prog_cnt_en;
  logic rd_cnt_en;
  logic beat_cnt_clr;
  logic [PageCntWidth-1:0] page_cnt, end_page;
  logic [WordCntWidth-1:0] word_cnt;
  logic [BeatCntWidth-1:0] beat_cnt;
  logic [WidthMultiple-1:0][BusWidth-1:0] prog_data;

  assign end_page = RmaWipeEntries[rma_wipe_idx].start_page +
                    RmaWipeEntries[rma_wipe_idx].num_pages;

  rma_state_e rma_state_d, rma_state_q;
  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [RmaStateWidth-1:0] rma_state_raw_q;
  assign rma_state_q = rma_state_e'(rma_state_raw_q);
  // SEC_CM: FSM.SPARSE
  prim_sparse_fsm_flop #(
    .StateEnumT(rma_state_e),
    .Width(RmaStateWidth),
    .ResetValue(RmaStateWidth'(StRmaIdle))
  ) u_rma_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( rma_state_d ),
    .state_o ( rma_state_raw_q )
  );

  // SEC_CM: CTR.SPARSE
  logic page_err_q, page_err_d;
  prim_count #(
    .Width(PageCntWidth),
    .OutSelDnCnt(1'b0),
    .CntStyle(prim_count_pkg::DupCnt)
  ) u_page_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(page_cnt_clr),
    .set_i(page_cnt_ld),
    .set_cnt_i(RmaWipeEntries[rma_wipe_idx].start_page),
    .en_i(page_cnt_incr),
    .step_i(PageCntWidth'(1)),
    .cnt_o(page_cnt),
    .err_o(page_err_d)
  );

  logic word_err_q, word_err_d;
  prim_count #(
    .Width(WordCntWidth),
    .OutSelDnCnt(1'b0),
    .CntStyle(prim_count_pkg::CrossCnt)
  ) u_word_cnt (
    .clk_i,
    .rst_ni,
    .clr_i(word_cnt_clr),
    .set_i(word_cnt_ld),
    .set_cnt_i(WordCntWidth'(BusWordsPerPage)),
    .en_i(word_cnt_incr),
    .step_i(WordCntWidth'(WidthMultiple)),
    .cnt_o(word_cnt),
    .err_o(word_err_d)
  );

  logic rma_idx_err_q, rma_idx_err_d;
  prim_count #(
    .Width(WipeIdxWidth),
    .OutSelDnCnt(1'b0),
    .CntStyle(prim_count_pkg::DupCnt)
  ) u_wipe_idx_cnt (
    .clk_i,
    .rst_ni,
    .clr_i('0),
    .set_i('0),
    .set_cnt_i('0),
    .en_i(rma_wipe_idx_incr),
    .step_i(WipeIdxWidth'(1'b1)),
    .cnt_o(rma_wipe_idx),
    .err_o(rma_idx_err_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      page_err_q <= '0;
      word_err_q <= '0;
      rma_idx_err_q <= '0;
    end else begin
      page_err_q <= page_err_q | page_err_d;
      word_err_q <= word_err_q | word_err_d;
      rma_idx_err_q <= rma_idx_err_q | rma_idx_err_d;
    end
  end

  // beat cnt is not made a prim_count because if beat_cnt
  // if tampered, the read verification stage will automatically
  // fail.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      beat_cnt <= '0;
    end else if (beat_cnt_clr) begin
      beat_cnt <= '0;
    end else if (prog_cnt_en) begin
      if (wvalid_o && wready_i) begin
        beat_cnt <= beat_cnt + 1'b1;
      end
    end else if (rd_cnt_en) begin
      if (rvalid_i && rready_o) begin
        beat_cnt <= beat_cnt + 1'b1;
      end
    end
  end

  // latch data programmed
  always_ff @(posedge clk_i) begin
    if (prog_cnt_en && wvalid_o && wready_i) begin
      prog_data[beat_cnt] <= rand_i;
    end
  end

  // once error is set to off, it cannot be unset without a reboot
  // On - no errors
  // Off - errors were observed
  logic [lc_ctrl_pkg::TxWidth-1:0] err_sts_raw_q;
  assign err_sts_q = lc_ctrl_pkg::lc_tx_t'(err_sts_raw_q);
  assign err_sts_d = err_sts_set && (err_sts_q != lc_ctrl_pkg::Off) ? lc_ctrl_pkg::Off : err_sts_q;
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

  logic rma_start;
  logic [BusAddrW-1:0] rma_addr;
  flash_op_e rma_op;
  flash_part_e rma_part_sel;
  logic [InfoTypesWidth-1:0] rma_info_sel;
  logic [11:0] rma_num_words;

  assign rma_addr = {RmaWipeEntries[rma_wipe_idx].bank,
                     page_cnt[PageW-1:0],
                     word_cnt[BusWordW-1:0]};

  assign rma_part_sel = RmaWipeEntries[rma_wipe_idx].part;
  assign rma_info_sel = RmaWipeEntries[rma_wipe_idx].info_sel;
  assign rma_num_words = WidthMultiple - 1;

  // this variable is specifically here to work around some tooling issues identified in #9661.
  // Certain tools identify rma_wipe_req as part of a combinational loop.
  // It is not a combinational loop in the synthesized sense, but rather a combinational loop from
  // the perspective of simulation scheduler.
  // This is not a synthesized combo loop for the following reasons
  // 1. rma_wipe_req is changed only based on the value of state_q, so it cannot be
  //    affected by non-flop signals
  // 2. other lint tools do not identify (including sign-off tool) an issue.
  // The direct feedthrough assignment below helps address some of the tooling issues.
  assign rma_wipe_req_int = rma_wipe_req;

  //fsm for handling the actual wipe
  logic fsm_err;

  // SEC_CM: RMA_ENTRY.MEM.SEC_WIPE
  always_comb begin
    rma_state_d = rma_state_q;
    rma_wipe_done = 1'b0;
    rma_start = 1'b0;
    rma_op = FlashOpInvalid;
    err_sts_set = 1'b0;
    page_cnt_ld = 1'b0;
    page_cnt_incr = 1'b0;
    page_cnt_clr = 1'b0;
    word_cnt_ld = 1'b0;
    word_cnt_incr = 1'b0;
    word_cnt_clr = 1'b0;
    prog_cnt_en = 1'b0;
    rd_cnt_en = 1'b0;
    beat_cnt_clr = 1'b0;
    fsm_err = 1'b0;

    unique case (rma_state_q)

      StRmaIdle: begin
        if (rma_wipe_req_int) begin
          rma_state_d = StRmaPageSel;
          page_cnt_ld = 1'b1;
        end
      end

      StRmaPageSel: begin
        if (page_cnt < end_page) begin
          rma_state_d = StRmaErase;
        end else begin
          rma_wipe_done = 1'b1;
          page_cnt_clr = 1'b1;
          rma_state_d = StRmaIdle;
        end
      end

      StRmaErase: begin
        rma_start = 1'b1;
        rma_op = FlashOpErase;
        if (done_i) begin
          err_sts_set = |err_i;
          rma_state_d = StRmaEraseWait;
        end
      end

      StRmaEraseWait: begin
         word_cnt_ld = 1'b1;
         rma_state_d = StRmaWordSel;
      end

      StRmaWordSel: begin
        if (word_cnt < BusWordsPerPage) begin
          rma_state_d = StRmaProgram;
        end else begin
          word_cnt_clr = 1'b1;
          page_cnt_incr = 1'b1;
          rma_state_d = StRmaPageSel;
        end
      end

      StRmaProgram: begin
        rma_start = 1'b1;
        rma_op = FlashOpProgram;
        prog_cnt_en = 1'b1;

        if ((beat_cnt == MaxBeatCnt[BeatCntWidth-1:0]) && wready_i) begin
          rma_state_d = StRmaProgramWait;
        end
      end

      StRmaProgramWait: begin
        rma_start = 1'b1;
        rma_op = FlashOpProgram;

        if (done_i) begin
          beat_cnt_clr = 1'b1;
          err_sts_set = |err_i;
          rma_state_d = StRmaRdVerify;
        end
      end

      StRmaRdVerify: begin
        rma_start = 1'b1;
        rma_op = FlashOpRead;
        rd_cnt_en = 1'b1;

        if ((beat_cnt == MaxBeatCnt[BeatCntWidth-1:0]) && done_i) begin
        //if ((beat_cnt == MaxBeatCnt[BeatCntWidth-1:0])) begin
          beat_cnt_clr = 1'b1;
          word_cnt_incr = 1'b1;
          rma_state_d = StRmaWordSel;
        end

        if (rvalid_i && rready_o) begin
          err_sts_set = prog_data[beat_cnt] != rdata_i;
        end
      end

      StRmaInvalid: begin
        err_sts_set = 1'b1;
        fsm_err = 1'b1;
      end

      default: begin
        rma_state_d = StRmaInvalid;
      end

    endcase // unique case (rma_state_q)
  end // always_comb

  assign wdata_o = rand_i;
  assign wvalid_o = prog_cnt_en;
  assign ctrl_o.start.q = seed_phase ? start : rma_start;
  assign ctrl_o.op.q = seed_phase ? op : rma_op;
  assign ctrl_o.prog_sel.q = prog_type;
  assign ctrl_o.erase_sel.q = erase_type;
  assign ctrl_o.partition_sel.q = seed_phase ? part_sel : rma_part_sel;
  assign ctrl_o.info_sel.q = seed_phase ? info_sel : rma_info_sel;
  assign ctrl_o.num = seed_phase ? num_words : rma_num_words;
  // address is consistent with software width format (full bus)
  assign addr_o = seed_phase ? {addr, {BusByteWidth{1'b0}}} :
                               {rma_addr, {BusByteWidth{1'b0}}};
  assign init_busy_o = seed_phase;
  assign req_o = seed_phase | rma_phase;
  assign rready_o = 1'b1;
  assign seeds_o = seeds_q;
  assign phase_o = phase;

  assign rma_ack_o = rma_ack_q;

  // all of these are considered fatal errors
  assign fatal_err_o = page_err_q | word_err_q | fsm_err | state_err | rma_idx_err_q;

  logic unused_seed_valid;
  assign unused_seed_valid = otp_key_rsp_i.seed_valid;

  // assertion

`ifdef INC_ASSERT
  logic [DataWidth-1:0] rma_data_q, rma_data;
  always_ff @(posedge clk_i) begin
    if (rma_start && rvalid_i && rready_o) begin
      rma_data_q <= rma_data;
    end
  end

  assign rma_data = {rdata_i, rma_data_q[DataWidth-1 : BusWidth]};

  // check the rma programmed value actually matches what was read back
  `ASSERT(ProgRdVerify_A, rma_start & rd_cnt_en & done_i |-> prog_data == rma_data)

`endif


endmodule // flash_ctrl_lcmgr
