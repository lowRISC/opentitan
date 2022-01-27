// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_sequencer extends uvm_sequencer#(rjtag_seq_item);

  `uvm_sequencer_utils(rjtag_sequencer)

  function new (string name, uvm_component parent);
    super.new(name,parent);
  endfunction : new

endclass : rjtag_sequencer
