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

module flash_phy_core import flash_ctrl_pkg::*; #(
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

  import flash_ctrl_pkg::*;
  import flash_phy_pkg::*;

  typedef enum logic [1:0] {
    StIdle,
    StRead,
    StCtrl
  } arb_state_e;

  arb_state_e state_q, state_d;

  // request signals to flash macro
  logic [PhyOps-1:0] reqs;

  // host select for address
  logic host_sel;

  // controller response valid
  logic ctrl_rsp_vld;

  // ack to phy operations from flash macro
  logic ack;

  // interface with flash macro
  logic [BankAddrW-1:0] muxed_addr;

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
    ctrl_rsp_vld = 1'b0;
    host_req_rdy_o = 1'b0;
    host_req_done_o = 1'b0;

    unique case (state_q)
      StIdle: begin
        if (host_req_i) begin
          host_req_rdy_o = 1'b1;
          host_sel = 1'b1;
          reqs[PhyRead] = 1'b1;
          state_d = StRead;
        end else if (req_i) begin
          reqs[PhyRead] = rd_i;
          reqs[PhyProg] = prog_i;
          reqs[PhyPgErase] = pg_erase_i;
          reqs[PhyBkErase] = bk_erase_i;
          state_d = StCtrl;
        end
      end

      StRead: begin
        if (ack) begin
          host_req_done_o = 1'b1;

          // pending read transaction, immediately start
          if (host_req_i) begin
            host_req_rdy_o = 1'b1;
            host_sel = 1'b1;
            reqs[PhyRead] = 1'b1;
          end else begin
            state_d = StIdle;
          end
        end
      end

      StCtrl: begin
        ctrl_rsp_vld = 1'b1;
        if (ack) begin
          state_d = StIdle;
        end
      end

      // state is terminal, no flash transactions are ever accepted again
      // until reboot
      default:;
    endcase // unique case (state_q)
  end

  assign muxed_addr       = host_sel ? host_addr_i : addr_i;
  assign rd_done_o = ctrl_rsp_vld & rd_i & ack;
  assign prog_done_o = ctrl_rsp_vld & prog_i & ack;
  assign erase_done_o = ctrl_rsp_vld & (pg_erase_i | bk_erase_i) & ack;

  // The actual flash macro wrapper
  prim_flash #(
    .PagesPerBank(PagesPerBank),
    .WordsPerPage(WordsPerPage),
    .DataWidth(DataWidth),
    .SkipInit(SkipInit)
  ) i_flash (
    .clk_i,
    .rst_ni,
    .rd_i(reqs[PhyRead]),
    .prog_i(reqs[PhyProg]),
    .pg_erase_i(reqs[PhyPgErase]),
    .bk_erase_i(reqs[PhyBkErase]),
    .addr_i(muxed_addr[0 +: PageW + WordW]),
    .prog_data_i(prog_data_i),
    .ack_o(ack),
    .rd_data_o,
    .init_busy_o // TBD this needs to be looked at later. What init do we need to do,
                 // and where does it make the most sense?
  );

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // requests to flash must always be one hot
  `ASSERT(OneHotReqs_A, $onehot0(reqs))

endmodule // flash_phy_core
