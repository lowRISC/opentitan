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

module flash_phy_core
import flash_phy_pkg::*;
#(
    parameter bit SkipInit = 1,  // this is an option to reset flash to all F's at reset
    parameter int ArbCnt = 4  // this is an option to reset flash to all F's at reset
) (
    input clk_i,
    input rst_ni,
    input scramble_en_i,  // temporary signal
    input host_req_i,  // host request - read only
    input [BusBankAddrW-1:0] host_addr_i,
    input req_i,  // controller request
    input rd_i,
    input prog_i,
    input pg_erase_i,
    input bk_erase_i,
    input flash_ctrl_pkg::flash_part_e part_i,
    input [BusBankAddrW-1:0] addr_i,
    input [BusWidth-1:0] prog_data_i,
    input prog_last_i,
    input [KeySize-1:0] addr_key_i,
    input [KeySize-1:0] data_key_i,
    output logic host_req_rdy_o,
    output logic host_req_done_o,
    output logic rd_done_o,
    output logic prog_done_o,
    output logic erase_done_o,
    output logic [BusWidth-1:0] rd_data_o,
    output logic init_busy_o
);


  localparam int CntWidth = $clog2(ArbCnt + 1);

  typedef enum logic [2:0] {
    StIdle,
    StHostRead,
    StCtrlRead,
    StCtrlProg,
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

  // ack from flash_phy_prog to controller
  logic prog_ack;

  // interface with flash macro
  logic [BusBankAddrW-1:0] muxed_addr;
  flash_ctrl_pkg::flash_part_e muxed_part;

  // entire read stage is idle, inclusive of all stages
  logic rd_stage_idle;

  // the read stage is ready to accept a new transaction
  logic rd_stage_rdy;

  // the read stage has valid data return
  logic rd_stage_data_valid;

  // arbitration counter
  // If controller side has lost arbitration ArbCnt times, favor it once
  logic [CntWidth-1:0] arb_cnt;
  logic inc_arb_cnt, clr_arb_cnt;
  logic host_req_masked;

  // scramble / de-scramble connections
  logic calc_ack;
  logic op_ack;
  logic [DataWidth-1:0] scramble_mask;

  assign host_req_masked = host_req_i & (arb_cnt < ArbCnt);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      arb_cnt <= '0;
    end else if (clr_arb_cnt) begin
      arb_cnt <= '0;
    end else if (inc_arb_cnt) begin
      arb_cnt <= arb_cnt + 1'b1;
    end
  end

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
    inc_arb_cnt = 1'b0;
    clr_arb_cnt = 1'b0;

    unique case (state_q)
      StIdle: begin
        if (host_req_masked) begin
          reqs[PhyRead] = 1'b1;
          host_sel = 1'b1;
          host_req_rdy_o = rd_stage_rdy;
          inc_arb_cnt = req_i & host_req_rdy_o;
          state_d = host_req_rdy_o ? StHostRead : state_q;
        end else if (req_i && rd_i) begin
          clr_arb_cnt = 1'b1;
          reqs[PhyRead] = 1'b1;
          state_d = rd_stage_rdy ? StCtrlRead : state_q;
        end else if (req_i && prog_i) begin
          clr_arb_cnt = 1'b1;
          reqs[PhyProg] = 1'b1;

          // it is possible for a program to immediate complete when the
          // program packing is not at the end of the flash word
          state_d = prog_ack ? StIdle : StCtrlProg;
          ctrl_rsp_vld = prog_ack;

        end else if (req_i) begin
          clr_arb_cnt = 1'b1;
          reqs[PhyPgErase] = pg_erase_i;
          reqs[PhyBkErase] = bk_erase_i;
          state_d = StCtrl;
        end
      end

      // The host has priority up to ArbCnt times when going head to head
      // with controller
      StHostRead: begin
        host_rsp = 1'b1;
        if (host_req_masked) begin
          reqs[PhyRead] = 1'b1;
          host_sel = 1'b1;
          host_req_rdy_o = rd_stage_rdy;
          inc_arb_cnt = req_i & host_req_rdy_o;
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

      // Controller program data may be packed based on
      // address alignment
      StCtrlProg: begin
        reqs[PhyProg] = 1'b1;
        if (prog_ack) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      // other controller operations directly interface with flash
      StCtrl: begin
        reqs[PhyPgErase] = pg_erase_i;
        reqs[PhyBkErase] = bk_erase_i;
        if (ack) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      // state is terminal, no flash transactions are ever accepted again
      // until reboot
      default:
      ;
    endcase  // unique case (state_q)
  end  // always_comb

  assign muxed_addr = host_sel ? host_addr_i : addr_i;
  assign muxed_part = host_sel ? flash_ctrl_pkg::FlashPartData : part_i;
  assign rd_done_o = ctrl_rsp_vld & rd_i;
  assign prog_done_o = ctrl_rsp_vld & prog_i;
  assign erase_done_o = ctrl_rsp_vld & (pg_erase_i | bk_erase_i);

  ////////////////////////
  // read pipeline
  ////////////////////////

  logic flash_rd_req;
  logic [DataWidth-1:0] flash_rdata;
  logic rd_calc_req;
  logic [BankAddrW-1:0] rd_calc_addr;
  logic rd_op_req;
  logic [DataWidth-1:0] rd_scrambled_data;
  logic [DataWidth-1:0] rd_descrambled_data;

  flash_phy_rd u_rd (
      .clk_i,
      .rst_ni,
      .req_i             (reqs[PhyRead]),
      .descramble_i      (scramble_en_i),
      .prog_i            (reqs[PhyProg]),
      .pg_erase_i        (reqs[PhyPgErase]),
      .bk_erase_i        (reqs[PhyBkErase]),
      .addr_i            (muxed_addr),
      .part_i            (muxed_part),
      .rdy_o             (rd_stage_rdy),
      .data_valid_o      (rd_stage_data_valid),
      .data_o            (rd_data_o),
      .idle_o            (rd_stage_idle),
      .req_o             (flash_rd_req),
      .ack_i             (ack),
      .data_i            (flash_rdata),
      //scramble unit interface
      .calc_req_o        (rd_calc_req),
      .calc_addr_o       (rd_calc_addr),
      .descramble_req_o  (rd_op_req),
      .scrambled_data_o  (rd_scrambled_data),
      .calc_ack_i        (calc_ack),
      .descramble_ack_i  (op_ack),
      .mask_i            (scramble_mask),
      .descrambled_data_i(rd_descrambled_data)
  );

  ////////////////////////
  // program pipeline
  ////////////////////////

  logic [DataWidth-1:0] prog_data, prog_scrambled_data;
  logic flash_prog_req;
  logic prog_calc_req;
  logic prog_op_req;

  if (WidthMultiple == 1) begin : gen_single_prog_data
    assign flash_prog_req = reqs[PhyProg];
    assign prog_data = prog_data_i;
  end else begin : gen_prog_data

    flash_phy_prog u_prog (
        .clk_i,
        .rst_ni,
        .req_i           (reqs[PhyProg]),
        .scramble_i      (scramble_en_i),
        .sel_i           (addr_i[0 +: WordSelW]),
        .data_i          (prog_data_i),
        .last_i          (prog_last_i),
        .ack_i           (ack),
        .calc_ack_i      (calc_ack),
        .scramble_ack_i  (op_ack),
        .mask_i          (scramble_mask),
        .scrambled_data_i(prog_scrambled_data),
        .calc_req_o      (prog_calc_req),
        .scramble_req_o  (prog_op_req),
        .req_o           (flash_prog_req),
        .ack_o           (prog_ack),
        .data_o          (prog_data)
    );

  end

  ////////////////////////
  // scrambling / de-scrambling primitive
  ////////////////////////

  logic [BankAddrW-1:0] scramble_muxed_addr;
  assign
      scramble_muxed_addr = prog_calc_req ? muxed_addr[BusBankAddrW - 1:LsbAddrBit] : rd_calc_addr;

  flash_phy_scramble u_scramble (
      .clk_i,
      .rst_ni,
      .calc_req_i      (prog_calc_req | rd_calc_req),
      .op_req_i        (prog_op_req | rd_op_req),
      .op_type_i       (prog_op_req ? ScrambleOp : DeScrambleOp),
      .addr_i          (scramble_muxed_addr),
      .plain_data_i    (prog_data),
      .scrambled_data_i(rd_scrambled_data),
      .addr_key_i      (addr_key_i),
      .data_key_i      (data_key_i),
      .calc_ack_o      (calc_ack),
      .op_ack_o        (op_ack),
      .mask_o          (scramble_mask),
      .plain_data_o    (rd_descrambled_data),
      .scrambled_data_o(prog_scrambled_data)
  );


  ////////////////////////
  // Actual connection to flash phy
  ////////////////////////

  wire [3:0] flash_test_mode_a;
  wire flash_test_voltage_h;

  assign flash_test_mode_a = '0;
  assign flash_test_voltage_h = '0;

  // The actual flash macro wrapper
  // The size of a page is fixed.  However, depending on the sizing of the word,
  // the number of words within a page will change.
  prim_flash #(
      .InfosPerBank(InfosPerBank),
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth),
      .SkipInit(SkipInit)
  ) i_flash (
      .clk_i,
      .rst_ni,
      .rd_i                 (flash_rd_req),
      .prog_i               (flash_prog_req),
      .pg_erase_i           (reqs[PhyPgErase]),
      .bk_erase_i           (reqs[PhyBkErase]),
      .addr_i               (muxed_addr[BusBankAddrW - 1:LsbAddrBit]),
      .part_i               (muxed_part),
      .prog_data_i          (prog_data),
      .ack_o                (ack),
      .rd_data_o            (flash_rdata),
      .init_busy_o,  // TBD this needs to be looked at later. What init do we need to do,
      // and where does it make the most sense?
      .tck_i                ('0),
      .tdi_i                ('0),
      .tms_i                ('0),
      .tdo_o                (),
      .scanmode_i           ('0),
      .scan_reset_ni        ('0),
      .flash_power_ready_hi ('0),
      .flash_power_down_hi  ('0),
      .flash_test_mode_ai   (flash_test_mode_a),
      .flash_test_voltage_hi(flash_test_voltage_h)
  );

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // requests to flash must always be one hot
  `ASSERT(OneHotReqs_A, $onehot0(reqs))
  `ASSERT_INIT(NoRemainder_A, AddrBitsRemain == 0)
  `ASSERT_INIT(Pow2Multiple_A, $onehot(WidthMultiple))

  `ASSERT(ArbCntMax_A, arb_cnt == ArbCnt |-> !inc_arb_cnt)
  `ASSERT(CtrlPrio_A, arb_cnt == ArbCnt |-> strong (##[0:20] clr_arb_cnt))

endmodule  // flash_phy_core
