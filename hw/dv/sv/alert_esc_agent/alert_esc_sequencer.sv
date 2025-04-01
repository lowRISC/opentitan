// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_esc_sequencer extends dv_base_sequencer#(alert_esc_seq_item, alert_esc_agent_cfg);
  `uvm_component_utils(alert_esc_sequencer)

  extern function new (string name="", uvm_component parent=null);

endclass : alert_esc_sequencer

function alert_esc_sequencer::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new
