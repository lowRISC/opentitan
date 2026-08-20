// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_sequencer extends dv_reactive_sequencer #(alert_seq_item, alert_agent_cfg);
  `uvm_component_utils(alert_sequencer)
  extern function new (string name, uvm_component parent);
endclass

function alert_sequencer::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction
