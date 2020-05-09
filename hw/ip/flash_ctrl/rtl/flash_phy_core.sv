// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Core Module
//
//
// This module wraps every single flash bank and contains most of the region attribute,
// scramble, ECC, security and arbitration logic.
// Most of the items are TODO, at the moment only arbitration logic exists.

module flash_phy_core import flash_phy_pkg::*; #(
  parameter bit SkipInit     = 1   // this is an option to reset flash to all F's at reset
) (
  input                        clk_i,
  input                        rst_ni,
  input                        host_req_i, // host request - read only
  input [BankAddrW-1:0]        host_addr_i,
  input                        req_i,      // controller request
  input                        rd_i,
  input                        prog_i,
  input                        pg_erase_i,
  input                        bk_erase_i,
  input [BankAddrW-1:0]        addr_i,
  input [BusWidth-1:0]         prog_data_i,
  output logic                 host_req_rdy_o,
  output logic                 host_req_done_o,
  output logic                 rd_done_o,
  output logic                 prog_done_o,
  output logic                 erase_done_o,
  output logic [BusWidth-1:0]  rd_data_o,
  output logic                 init_busy_o
);

  typedef enum logic [1:0] {
    StIdle,
    StHostRead,
    StCtrlRead,
    StCtrl
  } arb_state_e;

  arb_state_e state_q, state_d;

  // request signals to flash macro
  logic [PhyOps-1:0] reqs;

  // host select for address
  logic host_sel;

  // qualifier for host responses
  logic host_rsp;

  // controller response valid
  logic ctrl_rsp_vld;

  // ack to phy operations from flash macro
  logic ack;

  // interface with flash macro
  logic [BankAddrW-1:0] muxed_addr;

  // entire read stage is idle, inclusive of all stages
  logic rd_stage_idle;

  // the read stage is ready to accept a new transaction
  logic rd_stage_rdy;

  // the read stage has valid data return
  logic rd_stage_data_valid;


  assign host_req_done_o = host_rsp & rd_stage_data_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= StIdle;
    end else begin
      state_q <= state_d;
    end
  end

  always_comb begin
    state_d = state_q;

    reqs = '0;
    host_sel = 1'b0;
    host_rsp = 1'b0;
    ctrl_rsp_vld = 1'b0;
    host_req_rdy_o = 1'b0;

    unique case (state_q)
      StIdle: begin
        if (host_req_i) begin
          reqs[PhyRead] = 1'b1;
          host_sel = 1'b1;
          host_req_rdy_o = rd_stage_rdy;
          state_d = host_req_rdy_o ? StHostRead : state_q;
        end else if (req_i && rd_i) begin
          reqs[PhyRead] = 1'b1;
          state_d = rd_stage_rdy ? StCtrlRead : state_q;
        end else if (req_i) begin
          reqs[PhyProg] = prog_i;
          reqs[PhyPgErase] = pg_erase_i;
          reqs[PhyBkErase] = bk_erase_i;
          state_d = StCtrl;
        end
      end

      // The host priority may be dangerous, as it could lock-out controller initiated
      // operations. Need to think about whether this should be made round-robin.
      StHostRead: begin
        host_rsp = 1'b1;
        if (host_req_i) begin
          reqs[PhyRead] = 1'b1;
          host_sel = 1'b1;
          host_req_rdy_o = rd_stage_rdy;
        end else if (rd_stage_idle) begin
          // once in pipelined reads, need to wait for the entire pipeline
          // to drain before returning to perform other operations
          state_d = StIdle;
        end
      end

      // Controller reads are very slow.
      // Need to update controller end to take advantage of read pipeline.
      // Once that is done, the two read states can merge.
      StCtrlRead: begin
        if (rd_stage_data_valid) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      // other controller operations directly interface with flash
      StCtrl: begin
        if (ack) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      // state is terminal, no flash transactions are ever accepted again
      // until reboot
      default:;
    endcase // unique case (state_q)
  end

  assign muxed_addr = host_sel ? host_addr_i : addr_i;
  assign rd_done_o = ctrl_rsp_vld & rd_i;
  assign prog_done_o = ctrl_rsp_vld & prog_i;
  assign erase_done_o = ctrl_rsp_vld & (pg_erase_i | bk_erase_i);

  ////////////////////////
  // read pipeline
  ////////////////////////

  logic flash_rd_req;
  logic [DataWidth-1:0] flash_rdata;

  flash_phy_rd i_rd (
    .clk_i,
    .rst_ni,
    .req_i(reqs[PhyRead]),
    .prog_i(reqs[PhyProg]),
    .pg_erase_i(reqs[PhyPgErase]),
    .bk_erase_i(reqs[PhyBkErase]),
    .addr_i(muxed_addr),
    .rdy_o(rd_stage_rdy),
    .data_valid_o(rd_stage_data_valid),
    .data_o(rd_data_o),
    .idle_o(rd_stage_idle),
    .req_o(flash_rd_req),
    .ack_i(ack),
    .data_i(flash_rdata)
    );

  ////////////////////////
  // program pipeline
  ////////////////////////

  // Below code is temporary and does not account for scrambling
  logic [DataWidth-1:0] prog_data;

  if (WidthMultiple == 1) begin : gen_single_prog_data
    assign prog_data = prog_data_i;
  end else begin : gen_prog_data
    logic [WidthMultiple-1:0][BusWidth-1:0] prog_data_packed;

    always_comb begin
      prog_data_packed = {DataWidth{1'b1}};
      for (int i = 0; i < WidthMultiple; i++) begin
        if (addr_i[0 +: WordSelW] == i) begin
          prog_data_packed[i] = prog_data_i;
        end
      end
    end

    assign prog_data = prog_data_packed;
  end

  ////////////////////////
  // scrambling / de-scrambling primitive
  ////////////////////////


  ////////////////////////
  // Actual connection to flash phy
  ////////////////////////

  // The actual flash macro wrapper
  // The size of a page is fixed.  However, depending on the sizing of the word,
  // the number of words within a page will change.
  prim_flash #(
    .PagesPerBank(PagesPerBank),
    .WordsPerPage(WordsPerPage / WidthMultiple),
    .DataWidth(DataWidth),
    .SkipInit(SkipInit)
  ) i_flash (
    .clk_i,
    .rst_ni,
    .rd_i(flash_rd_req),
    .prog_i(reqs[PhyProg]),
    .pg_erase_i(reqs[PhyPgErase]),
    .bk_erase_i(reqs[PhyBkErase]),
    //.addr_i(muxed_addr[0 +: PageW + WordW]),
    .addr_i(muxed_addr[BankAddrW-1:LsbAddrBit]),
    .prog_data_i(prog_data),
    .ack_o(ack),
    .rd_data_o(flash_rdata),
    .init_busy_o // TBD this needs to be looked at later. What init do we need to do,
                 // and where does it make the most sense?
  );

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // requests to flash must always be one hot
  `ASSERT(OneHotReqs_A, $onehot0(reqs))
  `ASSERT_INIT(NoRemainder_A, AddrBitsRemain == 0)
  `ASSERT_INIT(Pow2Multiple_A, $onehot(WidthMultiple))

endmodule // flash_phy_core
