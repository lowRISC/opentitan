// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Open-source implementation of the vendor-specific RRAM TAP steps of the CP flow.
// A vendor implementation may provide its own version, see lowrisc:virtual_dv:rram_macro_forming.
// This file is included into the body of chip_rram_cp_flow_vseq.
// Every implementation defines these two tasks:
// - rram_tap_enable() runs through RV_DM SBA, before RRAM_JTAG_SEL selects the RRAM TAP.
// - vendor_forming_flow() runs on the RRAM TAP, through rram_tap_shift() of the sequence.

`ifndef RRAM_MACRO_FORMING_SVH
`define RRAM_MACRO_FORMING_SVH

// The open-source rram_macro TAP needs no enable.
virtual task rram_tap_enable();
endtask

// The open-source rram_macro has no forming.
// This only reads the IDCODE of its TAP, which shows that the RRAM TAP chain is reachable.
virtual task vendor_forming_flow();
  // Must match JtagIdcodeValue in the open-source rram_macro.sv.
  localparam bit [31:0] ExpIdcode = 32'h5252_414D;
  localparam uint IrLen = 5;
  localparam bit [IrLen-1:0] IrIdcode = 5'h01;
  bit [jtag_agent_pkg::JTAG_DRW-1:0] dout;
  rram_tap_shift(.ir_len(IrLen), .ir(IrIdcode), .dr_len(32), .dr('0), .dout(dout));
  `DV_CHECK_EQ(dout[31:0], ExpIdcode, "RRAM TAP IDCODE")
endtask

`endif // RRAM_MACRO_FORMING_SVH
