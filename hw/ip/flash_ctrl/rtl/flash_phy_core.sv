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

  // The operation sent to the flash macro
  flash_phy_op_sel_e op_sel;

  // The flash macro is currently idle
  logic flash_idle;

  // request signals to flash macro
  logic [PhyOps-1:0] reqs;

  // ack to phy operations from flash macro
  logic ack;

  // interface with flash macro
  logic [BankAddrW-1:0] muxed_addr;

  // valid request conditions
  logic op_clr_cond;

  logic host_sel;

  // flash is idle when no op is selected
  // or when the flash acks
  assign flash_idle = (op_sel == None) | ack;

  // if current operation is host, only transition to None if no more pending reqs
  // if current operation is ctrl, transition back whenever operation done
  assign op_clr_cond = (op_sel == Host) ? flash_idle & !host_req_i :
                       (op_sel == Ctrl) ? flash_idle : 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      op_sel <= None;
    end else if (op_clr_cond) begin
      op_sel <= None;
    end else if (flash_idle && host_req_i) begin
      op_sel <= Host;
    end else if (flash_idle && req_i) begin
      op_sel <= Ctrl;
    end
  end

  // controller read request has different timing from host_req.
  // The code below massages the two to be the same
  logic ctrl_rd_req;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_rd_req <= 1'b0;
    end else if (req_i && rd_i && op_sel == Ctrl) begin
      // drop read request once it has been accepted
      ctrl_rd_req <= 1'b0;
    end else if (req_i && rd_i && op_sel != Ctrl) begin
      // raise read request
      ctrl_rd_req <= 1'b1;
    end
  end

  // host is selected whenever current operation is none and there is a request
  // or if the pending operation is already host
  assign host_sel = (op_sel == None) ? host_req_i : (op_sel == Host);

  // host can only perform read transactions
  assign reqs[PhyRead]    = host_sel | ctrl_rd_req;
  assign reqs[PhyProg]    = !host_sel & req_i & prog_i;
  assign reqs[PhyPgErase] = !host_sel & req_i & pg_erase_i;
  assign reqs[PhyBkErase] = !host_sel & req_i & bk_erase_i;
  assign muxed_addr       = host_sel ? host_addr_i : addr_i;

  // whenever there is nothing selected, host transactions are always accepted
  // This also implies host trasnactions have the highest priority
  assign host_req_rdy_o  = (op_sel == None) | host_req_done_o;
  assign host_req_done_o = (op_sel == Host) & ack;
  assign rd_done_o       = (op_sel == Ctrl) & ack & rd_i;
  assign prog_done_o     = (op_sel == Ctrl) & ack & prog_i;
  assign erase_done_o    = (op_sel == Ctrl) & ack & (pg_erase_i | bk_erase_i);

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

  // if op_sel is Ctrl, it must have come from None
  `ASSERT(CtrlPrevNone_A, $rose(op_sel == Ctrl) |-> $past(op_sel == None))

  // if no operation is ongoing, a host request must always win
  `ASSERT(HostPriority_A, (op_sel == None) && host_req_i |=> op_sel == Host)

  // if a host request is done, and is immediately followed by another host request
  // host should retain priority
  `ASSERT(HostPriorityConseq_A, (op_sel == Host && flash_idle) && host_req_i |=> op_sel == Host)

  // host request should never interrupt an ongoing controller operation
  `ASSERT(CtrlAtomic_A, op_sel == Ctrl && !flash_idle |=> op_sel == Ctrl)

  // ctrl request do not allow overlapping
  `ASSERT(CtrlSerial_A, op_sel == Ctrl && flash_idle |=> op_sel == None)

endmodule // flash_phy_core
