// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register slice conforming to Comportibility guide.

module prim_subreg #(
  parameter int            DW       = 32  ,
  parameter                SWACCESS = "RW",  // {RW, RO, WO, W1C, W1S, W0C, RC}
  parameter logic [DW-1:0] RESVAL   = '0     // Reset value
) (
  input clk_i,
  input rst_ni,

  // From SW: valid for RW, WO, W1C, W1S, W0C, RC
  // In case of RC, Top connects Read Pulse to we
  input          we,
  input [DW-1:0] wd,

  // From HW: valid for HRW, HWO
  input          de,
  input [DW-1:0] d,

  // output to HW and Reg Read
  output logic          qe,
  output logic [DW-1:0] q,
  output logic [DW-1:0] qs
);

  logic          wr_en ;
  logic [DW-1:0] wr_data;

  if ((SWACCESS == "RW") || (SWACCESS == "WO")) begin : gen_w
    assign wr_en   = we | de ;
    assign wr_data = (we == 1'b1) ? wd : d ; // SW higher priority
  end else if (SWACCESS == "RO") begin : gen_ro
    // Unused we, wd
    assign wr_en   = de ;
    assign wr_data = d  ;
  end else if (SWACCESS == "W1S") begin : gen_w1s
    // If SWACCESS is W1S, then assume hw tries to clear.
    // So, give a chance HW to clear when SW tries to set.
    // If both try to set/clr at the same bit pos, SW wins.
    assign wr_en   = we | de ;
    assign wr_data = (de ? d : q) | (we ? wd : '0);
  end else if (SWACCESS == "W1C") begin : gen_w1c
    // If SWACCESS is W1C, then assume hw tries to set.
    // So, give a chance HW to set when SW tries to clear.
    // If both try to set/clr at the same bit pos, SW wins.
    assign wr_en   = we | de ;
    assign wr_data = (de ? d : q) & (we ? ~wd : '1);
  end else if (SWACCESS == "W0C") begin : gen_w0c
    assign wr_en   = we | de ;
    assign wr_data = (de ? d : q) & (we ? wd : '1);
  end else if (SWACCESS == "RC") begin : gen_rc
    // This swtype is not recommended but exists for compatibility.
    // WARN: we signal is actually read signal not write enable.
    assign wr_en  = we | de ;
    assign wr_data = (de ? d : q) & (we ? '0 : '1);
  end else begin : gen_hw
    assign wr_en   = de ;
    assign wr_data = d  ;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) qe <= 1'b0;
    else        qe <= we  ;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)     q <= RESVAL ;
    else if (wr_en) q <= wr_data;
  end
  assign qs = q;

endmodule
