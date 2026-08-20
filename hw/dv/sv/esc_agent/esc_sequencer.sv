// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class esc_sequencer extends dv_reactive_sequencer #(esc_seq_item, esc_agent_cfg);
  `uvm_component_utils(esc_sequencer)

  extern function new (string name, uvm_component parent);

endclass : esc_sequencer

function esc_sequencer::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new
