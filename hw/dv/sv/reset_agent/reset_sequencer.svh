// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_sequencer extends dv_base_sequencer #(
  .ITEM_T (reset_item),
  .CFG_T  (reset_agent_cfg)
);
  `uvm_sequencer_utils(reset_sequencer)

// Standard SV/UVM methods
extern function new(string name, uvm_component parent = null);
endclass : reset_sequencer


function reset_sequencer::new(string name, uvm_component parent = null);
  super.new(name, parent);
endfunction : new
