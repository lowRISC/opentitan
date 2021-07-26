// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Write enable and data arbitration logic for register slice conforming to Comportibility guide.

module prim_subreg_arb
  import prim_subreg_pkg::*;
#(
  parameter int         DW       = 32,
  parameter sw_access_e SwAccess = SwAccessRW
) (
  // From SW: valid for RW, WO, W1C, W1S, W0C, RC.
  // In case of RC, top connects read pulse to we.
  input          we,
  input [DW-1:0] wd,

  // From HW: valid for HRW, HWO.
  input          de,
  input [DW-1:0] d,

  // From register: actual reg value.
  input [DW-1:0] q,

  // To register: actual write enable and write data.
  output logic          wr_en,
  output logic [DW-1:0] wr_data
);

  if (SwAccess inside {SwAccessRW, SwAccessWO}) begin : gen_w
    assign wr_en   = we | de;
    assign wr_data = (we == 1'b1) ? wd : d; // SW higher priority
    // Unused q - Prevent lint errors.
    logic [DW-1:0] unused_q;
    assign unused_q = q;
  end else if (SwAccess == SwAccessRO) begin : gen_ro
    assign wr_en   = de;
    assign wr_data = d;
    // Unused we, wd, q - Prevent lint errors.
    logic          unused_we;
    logic [DW-1:0] unused_wd;
    logic [DW-1:0] unused_q;
    assign unused_we = we;
    assign unused_wd = wd;
    assign unused_q  = q;
  end else if (SwAccess == SwAccessW1S) begin : gen_w1s
    // If SwAccess is W1S, then assume hw tries to clear.
    // So, give a chance HW to clear when SW tries to set.
    // If both try to set/clr at the same bit pos, SW wins.
    assign wr_en   = we | de;
    assign wr_data = (de ? d : q) | (we ? wd : '0);
  end else if (SwAccess == SwAccessW1C) begin : gen_w1c
    // If SwAccess is W1C, then assume hw tries to set.
    // So, give a chance HW to set when SW tries to clear.
    // If both try to set/clr at the same bit pos, SW wins.
    assign wr_en   = we | de;
    assign wr_data = (de ? d : q) & (we ? ~wd : '1);
  end else if (SwAccess == SwAccessW0C) begin : gen_w0c
    assign wr_en   = we | de;
    assign wr_data = (de ? d : q) & (we ? wd : '1);
  end else if (SwAccess == SwAccessRC) begin : gen_rc
    // This swtype is not recommended but exists for compatibility.
    // WARN: we signal is actually read signal not write enable.
    assign wr_en  = we | de;
    assign wr_data = (de ? d : q) & (we ? '0 : '1);
    // Unused wd - Prevent lint errors.
    logic [DW-1:0] unused_wd;
    assign unused_wd = wd;
  end else begin : gen_hw
    assign wr_en   = de;
    assign wr_data = d;
    // Unused we, wd, q - Prevent lint errors.
    logic          unused_we;
    logic [DW-1:0] unused_wd;
    logic [DW-1:0] unused_q;
    assign unused_we = we;
    assign unused_wd = wd;
    assign unused_q  = q;
  end

endmodule
