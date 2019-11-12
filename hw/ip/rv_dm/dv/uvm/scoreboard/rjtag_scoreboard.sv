// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_scoreboard extends uvm_scoreboard;

  `uvm_component_utils(rjtag_scoreboard)
  uvm_analysis_imp#(rjtag_seq_item, rjtag_scoreboard) item_collected_export;

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    item_collected_export = new("item_collected_export", this);
  endfunction : build_phase

  virtual function void write(rjtag_seq_item pkt);
    pkt.print();
  endfunction : write

endclass : rjtag_scoreboard
