// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The mux to select between ROM inputs
//

module rom_ctrl_mux #(
  parameter int AW = 8
) (
  input logic           clk_i,
  input logic           rst_ni,

  // select signal. 1 = checker; 0 = bus
  input logic           sel_i,

  // Interface for bus
  input logic [AW-1:0]  bus_addr_i,
  input logic           bus_req_i,
  output logic          bus_gnt_o,
  output logic [38:0]   bus_rdata_o,
  output logic          bus_rvalid_o,

  // Interface for ROM checker
  input logic [AW-1:0]  chk_addr_i,
  input logic           chk_req_i,
  output logic [39:0]   chk_rdata_o,

  // Interface for ROM
  output logic [AW-1:0] rom_addr_o,
  output logic          rom_req_o,
  input logic [39:0]    rom_scr_rdata_i,
  input logic [39:0]    rom_clr_rdata_i,
  input logic           rom_rvalid_i,

  // Alert output
  output logic          alert_o
);

  // TODO: sel_q will definitely need to be multi-bit for glitch resistance. We'll probably also
  // have to chase the "signal bit signals" back a bit further through the logic too.
  logic sel_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sel_q <= 1'b1;
    end else begin
      sel_q  <= sel_q & sel_i;
    end
  end

  // Spot if the select signal becomes one again after it went to zero
  assign alert_o = sel_i & ~sel_q;

  // The bus can have access every cycle, once the select signal is zero.
  assign bus_gnt_o    = ~sel_i;
  assign bus_rdata_o  = rom_clr_rdata_i[38:0];
  // A high rom_rvalid_i is a response to a bus request if sel_i was zero on the previous cycle.
  assign bus_rvalid_o = ~sel_q & rom_rvalid_i;

  assign chk_rdata_o = rom_scr_rdata_i;

  assign rom_addr_o = sel_i ? chk_addr_i : bus_addr_i;
  assign rom_req_o  = sel_i ? chk_req_i  : bus_req_i;

  // We use a Hsiao (39,32) ECC scheme for data integrity, but have expanded the ROM to 40 bits
  // rather than 39 bits (it's no more expensive with many macro libraries, and it's slightly nicer
  // for scrambling, because 40 is a whole number of 4-bit sboxes). Of course, this means that we
  // never actually pass the top bit through to the bus. Waive that here.
  logic unused_bus_rdata_top;
  assign unused_bus_rdata_top = rom_clr_rdata_i[39];

endmodule
