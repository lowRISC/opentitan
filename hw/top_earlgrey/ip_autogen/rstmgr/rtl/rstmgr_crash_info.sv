// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// This module implements the crash dump functionality

`include "prim_assert.sv"

module rstmgr_crash_info
  import rstmgr_pkg::*;
  import rstmgr_reg_pkg::IdxWidth;
  import rstmgr_reg_pkg::RdWidth;
#(
  parameter  int CrashDumpWidth = 32,
  localparam int CrashRemainder = CrashDumpWidth % RdWidth > 0 ? 1 : 0,
  localparam int unsigned CrashStoreSlot = CrashDumpWidth / RdWidth + CrashRemainder,
  localparam int SlotCntWidth   = $clog2(CrashStoreSlot)
) (
  input clk_i,
  input rst_ni,
  input [CrashDumpWidth-1:0] dump_i,
  input dump_capture_i,
  input [IdxWidth-1:0] slot_sel_i,
  output logic [IdxWidth-1:0] slots_cnt_o,
  output logic [RdWidth-1:0] slot_o
);

  localparam int TotalWidth = CrashStoreSlot * RdWidth;
  logic [2**SlotCntWidth-1:0][RdWidth-1:0] slots;
  logic [ CrashStoreSlot-1:0][RdWidth-1:0] slots_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      slots_q <= '0;
    end else if (dump_capture_i) begin
      slots_q <= TotalWidth'(dump_i);
    end
  end

  always_comb begin
    slots = '0;
    slots[CrashStoreSlot-1:0] = slots_q;
  end

  assign slots_cnt_o = CrashStoreSlot[IdxWidth-1:0];
  assign slot_o = slots[slot_sel_i[SlotCntWidth-1:0]];

  if (SlotCntWidth < IdxWidth) begin : gen_tieoffs
    //VCS coverage off
    // pragma coverage off
    logic [IdxWidth-SlotCntWidth-1:0] unused_idx;
    assign unused_idx = slot_sel_i[IdxWidth-1:SlotCntWidth];
    //VCS coverage on
    // pragma coverage on
  end

  // Make sure the crash dump isn't excessively large
  `ASSERT_INIT(CntStoreSlot_A, CrashStoreSlot < (1 << IdxWidth))
  `ASSERT_INIT(CntWidth_A, SlotCntWidth <= IdxWidth)

endmodule  // rstmgr_crash_info
