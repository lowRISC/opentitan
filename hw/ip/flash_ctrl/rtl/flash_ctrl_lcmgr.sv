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
  output logic init_done_o,

  // only access seeds when provisioned
  input provision_en_i,

  // interface to ctrl arb control ports
  output flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t ctrl_o,
  output logic req_o,
  output logic [top_pkg::TL_AW-1:0] addr_o,
  input done_i,
  input err_i,

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

  // error status to registers
  output logic seed_err_o,

  // enable read buffer in flash_phy
  output logic rd_buf_en_o,

  // request otp keys
  output otp_ctrl_pkg::flash_otp_key_req_t otp_key_req_o,
  input otp_ctrl_pkg::flash_otp_key_rsp_t otp_key_rsp_i,
  output flash_key_t addr_key_o,
  output flash_key_t data_key_o,

  // entropy interface
  output logic edn_req_o,
  input edn_ack_i,
  output logic lfsr_en_o,
  input [BusWidth-1:0] rand_i,

  // init ongoing
  output logic init_busy_o
);

  // total number of pages to be wiped during RMA entry
  localparam int WipeIdxWidth = prim_util_pkg::vbits(WipeEntries);

  // seed related local params
  localparam int SeedReads = SeedWidth / BusWidth;
  localparam int SeedRdsWidth = $clog2(SeedReads);
  localparam int SeedCntWidth = $clog2(NumSeeds+1);
  localparam int NumSeedWidth = $clog2(NumSeeds);

  // the various seed outputs
  logic [NumSeeds-1:0][SeedReads-1:0][BusWidth-1:0] seeds_q;

  // progress through and read out the various pieces of content
  // This FSM should become sparse, especially for StRmaRsp
  typedef enum logic [3:0] {
    StIdle,
    StReqAddrKey,
    StReqDataKey,
    StReadSeeds,
    StWait,
    StEntropyReseed,
    StRmaWipe,
    StRmaRsp,
    StInvalid
  } state_e;

  state_e state_q, state_d;
  lc_ctrl_pkg::lc_tx_t err_sts;
  logic err_sts_set;
  lc_ctrl_pkg::lc_tx_t rma_ack_d, rma_ack_q;
  logic init_done_d;
  logic validate_q, validate_d;
  logic [SeedCntWidth-1:0] seed_cnt_q;
  logic [SeedRdsWidth-1:0] addr_cnt_q;
  logic seed_cnt_en, seed_cnt_clr;
  logic addr_cnt_en, addr_cnt_clr;
  logic rma_wipe_req, rma_wipe_done;
  logic [WipeIdxWidth-1:0] rma_wipe_idx;
  logic rma_wipe_idx_incr;
  flash_lcmgr_phase_e phase;
  logic seed_phase;
  logic rma_phase;

  assign seed_phase = phase == PhaseSeed;
  assign rma_phase = phase == PhaseRma;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StIdle;
      rma_ack_q <= lc_ctrl_pkg::Off;
      validate_q <= 1'b0;
      init_done_o <= 1'b0;
    end else begin
      state_q <= state_d;
      rma_ack_q <= rma_ack_d;
      validate_q <= validate_d;
      init_done_o <= init_done_d;
    end
  end

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
  lc_ctrl_pkg::lc_tx_t rma_req;

  prim_flop_2sync #(
    .Width(1),
    .ResetValue(0)
  ) u_sync_flash_init (
    .clk_i,
    .rst_ni,
    .d_i(init_i),
    .q_o(init_q)
  );

  prim_lc_sync #(
    .NumCopies(1)
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
      end

      if (data_key_req_d && data_key_ack_q) begin
        data_key_o <= flash_key_t'(otp_key_rsp_i.key);
      end
    end
  end


  ///////////////////////////////
  // Hardware Interface FSM
  // TODO: Merge the read/verify mechanism with RMA later
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
    num_words = SeedReads - 1'b1;

    // seed status
    seed_err_o = 1'b0;

    state_d = state_q;
    rma_ack_d = lc_ctrl_pkg::Off;
    validate_d = validate_q;

    // read buffer enable
    rd_buf_en_o = 1'b0;

    // init status
    // flash_ctrl handles its own arbitration between hardware and software.
    // So once the init kicks off it is safe to ack.  The done signal is still
    // to give a chance to hold off further power up progression in the future
    // if required.
    init_done_d = 1'b1;

    addr_key_req_d = 1'b0;
    data_key_req_d = 1'b0;

    // entropy handling
    edn_req_o = 1'b0;
    lfsr_en_o = 1'b0;

    // rma related
    rma_wipe_req = 1'b0;
    rma_wipe_idx_incr = 1'b0;

    unique case (state_q)

      StIdle: begin
        init_done_d = 1'b0;
        phase = PhaseSeed;
        if (init_q) begin
          state_d = StReqAddrKey;
        end
      end

      StReqAddrKey: begin
        addr_key_req_d = 1'b1;
        if (addr_key_ack_q) begin
          state_d = StReqDataKey;
        end
      end

      StReqDataKey: begin
        data_key_req_d = 1'b1;
        if (data_key_ack_q) begin
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
        if (seed_cnt_q == NumSeeds) begin
          start = 1'b0;
          state_d = StWait;

        // still reading curent seed, increment whenever data returns
        end else if (!done_i) begin
          addr_cnt_en = rvalid_i;

        // current seed reading is complete
        // error is intentionally not used here, as we do not want read seed
        // failures to stop the software from using flash
        // When there are upstream failures, the data returned is simply all 1's.
        // So instead of doing anything explicit, a status is indicated for software.
        end else if (done_i) begin
          addr_cnt_clr = 1'b1;
          seed_err_o = 1'b1;

          // we move to the next seed only if current seed is read and validated
          // if not, flip to validate phase and read seed again
          if (validate_q) begin
            seed_cnt_en = 1'b1;
            validate_d = 1'b0;
          end else begin
            validate_d = 1'b1;
          end
        end
      end

      // Waiting for an rma entry command
      StWait: begin
        rd_buf_en_o = 1'b1;
        if (rma_req == lc_ctrl_pkg::On) begin
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

        if (rma_wipe_idx == WipeEntries-1 && rma_wipe_done) begin
          // first check for error status
          // If error status is set, go directly to invalid terminal state
          // If error status is good, go to second check
          state_d = (err_sts != lc_ctrl_pkg::On) ? StInvalid : StRmaRsp;
        end else if (rma_wipe_done) begin
          rma_wipe_idx_incr = 1;
        end
      end

      // response to rma request
      // Second check for error status:
      // If error status indicates error, jump to invalid terminal state
      // Otherwise assign output to error status;
      // TODO: consider lengthening the check
      StRmaRsp: begin
        phase = PhaseRma;
        if (err_sts != lc_ctrl_pkg::On) begin
          state_d = StInvalid;
        end else begin
          rma_ack_d = err_sts;
        end
      end

      // Invalid catch-all state
      default: begin
        phase = PhaseInvalid;
        rma_ack_d = lc_ctrl_pkg::Off;
        state_d = StInvalid;
      end

    endcase // unique case (state_q)

  end // always_comb

  ///////////////////////////////
  // RMA wiping Mechanism
  ///////////////////////////////

  localparam int PageCntWidth = prim_util_pkg::vbits(PagesPerBank + 1);
  localparam int WordCntWidth = prim_util_pkg::vbits(BusWordsPerPage + 1);
  localparam int BeatCntWidth = prim_util_pkg::vbits(WidthMultiple);

  logic page_cnt_ld;
  logic page_cnt_incr;
  logic page_cnt_clr;
  logic word_cnt_incr;
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

  typedef enum logic [2:0] {
    StRmaIdle,
    StRmaPageSel,
    StRmaErase,
    StRmaWordSel,
    StRmaProgram,
    StRmaProgramWait,
    StRmaRdVerify
  } rma_state_e;

  rma_state_e rma_state_d, rma_state_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rma_state_q <= StRmaIdle;
    end else begin
      rma_state_q <= rma_state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      page_cnt <= '0;
    end else if (page_cnt_clr) begin
      page_cnt <= '0;
    end else if (page_cnt_ld) begin
      page_cnt <= RmaWipeEntries[rma_wipe_idx].start_page;
    end else if (page_cnt_incr) begin
      page_cnt <= page_cnt + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      word_cnt <= '0;
    end else if (word_cnt_clr) begin
      word_cnt <= '0;
    end else if (word_cnt_incr) begin
      word_cnt <= word_cnt + WidthMultiple;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rma_wipe_idx <= '0;
    end else if (rma_wipe_idx_incr) begin
      rma_wipe_idx <= rma_wipe_idx + 1'b1;
    end
  end

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
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_sts <= lc_ctrl_pkg::On;
    end else if (err_sts_set && (err_sts != lc_ctrl_pkg::Off)) begin
      err_sts <= lc_ctrl_pkg::Off;
    end
  end

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


  //fsm for handling the actual wipe
  always_comb begin
    rma_state_d = rma_state_q;
    rma_wipe_done = 1'b0;
    rma_start = 1'b0;
    rma_op = FlashOpInvalid;
    err_sts_set = 1'b0;
    page_cnt_ld = 1'b0;
    page_cnt_incr = 1'b0;
    page_cnt_clr = 1'b0;
    word_cnt_incr = 1'b0;
    word_cnt_clr = 1'b0;
    prog_cnt_en = 1'b0;
    rd_cnt_en = 1'b0;
    beat_cnt_clr = 1'b0;

    unique case (rma_state_q)

      StRmaIdle: begin
        if (rma_wipe_req) begin
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
          err_sts_set = err_i;
          rma_state_d = StRmaWordSel;
        end
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

        if ((beat_cnt == WidthMultiple-1) && wready_i) begin
          rma_state_d = StRmaProgramWait;
        end
      end

      StRmaProgramWait: begin
        rma_start = 1'b1;
        rma_op = FlashOpProgram;

        if (done_i) begin
          beat_cnt_clr = 1'b1;
          err_sts_set = err_i;
          rma_state_d = StRmaRdVerify;
        end
      end

      StRmaRdVerify: begin
        rma_start = 1'b1;
        rma_op = FlashOpRead;
        rd_cnt_en = 1'b1;

        if ((beat_cnt == WidthMultiple-1) && done_i) begin
          beat_cnt_clr = 1'b1;
          word_cnt_incr = 1'b1;
          rma_state_d = StRmaWordSel;
        end

        if (rvalid_i && rready_o) begin
          err_sts_set = prog_data[beat_cnt] != rdata_i;
        end
      end

      default: begin
        err_sts_set = 1'b1;
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
  assign addr_o = seed_phase ? top_pkg::TL_AW'({addr, {BusByteWidth{1'b0}}}) :
                               top_pkg::TL_AW'({rma_addr, {BusByteWidth{1'b0}}});
  assign init_busy_o = seed_phase;
  assign req_o = seed_phase | rma_phase;
  assign rready_o = 1'b1;
  assign seeds_o = seeds_q;
  assign phase_o = phase;

  assign rma_ack_o = rma_ack_q;

  logic unused_seed_valid;
  assign unused_seed_valid = otp_key_rsp_i.seed_valid;

endmodule // flash_ctrl_lcmgr
