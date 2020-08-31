// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Controller for life cycle / key management handling
//

module flash_ctrl_lcmgr import flash_ctrl_pkg::*; (
  input clk_i,
  input rst_ni,

  // interface to ctrl arb control ports
  output flash_ctrl_reg_pkg::flash_ctrl_reg2hw_control_reg_t ctrl_o,
  output logic req_o,
  output logic [top_pkg::TL_AW-1:0] addr_o,
  input done_i,
  input err_i,

  // interface to ctrl_arb data ports
  output logic rready_o,
  input rvalid_i,

  // direct form rd_fifo
  input [BusWidth-1:0] rdata_i,

  // external rma request
  input rma_i,
  input [BusWidth-1:0] rma_token_i, // just a random string
  output logic [BusWidth-1:0] rma_token_o,
  output logic rma_rsp_o,

  // random value
  input [BusWidth-1:0] rand_i,

  // seeds to the outside world,
  output logic [NumSeeds-1:0][SeedWidth-1:0] seeds_o,

  // init ongoing
  output logic init_busy_o
);

  // total number of pages to be wiped during RMA entry
  localparam int TotalDataPages = NumBanks * PagesPerBank;
  localparam int CntWidth = $clog2(TotalDataPages + 1);

  // seed related local params
  localparam int SeedReads = SeedWidth / BusWidth;
  localparam int SeedRdsWidth = $clog2(SeedReads);
  localparam int SeedCntWidth = $clog2(NumSeeds+1);
  localparam int NumSeedWidth = $clog2(NumSeeds);

  // the various seed outputs
  logic [NumSeeds-1:0][SeedReads-1:0][BusWidth-1:0] seeds_q;

  // rma related functions
  logic [1:0][BusWidth-1:0] rsp_token;

  // progress through and read out the various pieces of content
  // This FSM should become sparse, especially for StRmaRsp
  typedef enum logic [3:0] {
    StReadSeeds,
    StWait,
    StWipeOwner,
    StWipeDataPart,
    StRmaRsp
  } state_e;

  state_e state_q, state_d;
  logic validate_q, validate_d;
  logic [SeedCntWidth-1:0] seed_cnt_q;
  logic [CntWidth-1:0] addr_cnt_q;
  logic seed_cnt_en, seed_cnt_clr;
  logic addr_cnt_en, addr_cnt_clr;
  logic seed_phase;
  logic rma_phase;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StReadSeeds;
      validate_q <= 1'b0;
    end else begin
      state_q <= state_d;
      validate_q <= validate_d;
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

  // capture the random token for return
  // store token in 2-shares and continuously xor in data
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rsp_token <= '0;
    end else if (rma_i) begin
      rsp_token[0] <= rma_token_i ^ rand_i ^ BusWidth'(StRmaRsp);
      rsp_token[1] <= rand_i;
    // token can be changed during validation portion of the rma phase
    end else if (rma_phase && validate_q && rvalid_i) begin
      rsp_token <= rsp_token ^ {rdata_i, rdata_i};
    end
  end


  logic [BusAddrW-1:0] seed_page_addr;
  assign seed_page_addr = BusAddrW'({SeedInfoPageSel[seed_idx], BusWordW'(0)});

  logic [BusAddrW-1:0] owner_page_addr;
  assign owner_page_addr = BusAddrW'({logic'(OwnerInfoPage), BusWordW'(0)});

  logic start;
  flash_op_e op;
  flash_erase_e erase_type;
  flash_part_e part_sel;
  logic [11:0] num_words;
  logic [BusAddrW-1:0] addr;
  logic [BusWidth-1:0] rsp_mask;

  assign erase_type = FlashErasePage;
  // seed phase is always read
  // rma phase is erase unless we are validating
  assign op = seed_phase || validate_q ? FlashOpRead : FlashOpErase;

  always_comb begin

    // phases of the hardware interface
    seed_phase = 1'b0;
    rma_phase = 1'b0;

    // timer controls
    seed_cnt_en = 1'b0;
    seed_cnt_clr = 1'b0;
    addr_cnt_en = 1'b0;
    addr_cnt_clr = 1'b0;

    // flash ctrrl arb controls
    start = 1'b0;
    addr = '0;
    part_sel = FlashPartInfo;
    num_words = SeedReads - 1'b1;

    // rma responses
    rma_rsp_o = 1'b0;
    rsp_mask = {BusWidth{1'b1}};

    state_d = state_q;
    validate_d = validate_q;

    unique case (state_q)

      // read seeds
      StReadSeeds: begin
        // seeds can be updated in this state
        seed_phase = 1'b1;

        // kick off flash transaction
        start = 1'b1;
        addr = BusAddrW'(seed_page_addr);

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
        // TBD add handling of seeds for error conditions
        end else if (done_i) begin
          addr_cnt_clr = 1'b1;

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
        if (rma_i) begin
          state_d = StWipeOwner;
        end
      end

      // wipe away owner seed partition
      StWipeOwner: begin
        rma_phase = 1'b1;
        start = 1'b1;
        addr = BusAddrW'(owner_page_addr);
        num_words = BusWordsPerPage - 1'b1;

        if (done_i && !err_i) begin
          // if validate flag is set, erase and validation completed, proceed
          // if validate flag not set, begin validation
          if (validate_q) begin
            validate_d = 1'b0;
            state_d = StWipeDataPart;
          end else begin
            validate_d = 1'b1;
          end
        end
      end

      // wipe away data partitions
      StWipeDataPart: begin
        rma_phase = 1'b1;
        part_sel = FlashPartData;
        start = 1'b1;
        addr = BusAddrW'({addr_cnt_q, BusWordW'(0)});
        num_words = BusWordsPerPage - 1'b1;

        // reached the final page
        if (addr_cnt_q == TotalDataPages) begin
          start = 1'b0;
          addr_cnt_clr = 1'b1;

          // completed wiping and validation, proceed
          if (validate_q) begin
            state_d = StRmaRsp;
            validate_d = 1'b0;
          // completed wiping, begin validation
          end else begin
            validate_d = 1'b1;
          end

        // still working through erasing / validating pages
        end else if (done_i && !err_i) begin
          addr_cnt_en = 1'b1;
        end
      end

      // response to rma request
      StRmaRsp: begin
        rma_phase = 1'b1;
        rma_rsp_o = 1'b1;
        rsp_mask = BusWidth'(StRmaRsp);
      end

      default:;
    endcase // unique case (state_q)

  end // always_comb

  assign rma_token_o = rsp_token[0] ^ rsp_token[1] ^ rsp_mask;
  assign ctrl_o.start.q = start;
  assign ctrl_o.op.q = op;
  assign ctrl_o.erase_sel.q = erase_type;
  assign ctrl_o.partition_sel.q = part_sel;
  assign ctrl_o.num = num_words;
  // address is consistent with software width format (full bus)
  assign addr_o = top_pkg::TL_AW'({addr, {BusByteWidth{1'b0}}});
  assign init_busy_o = seed_phase;
  assign req_o = seed_phase | rma_phase;
  assign rready_o = 1'b1;
  assign seeds_o = seeds_q;

endmodule // flash_ctrl_lcmgr
