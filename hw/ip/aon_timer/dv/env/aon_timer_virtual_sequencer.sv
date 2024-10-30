// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(aon_timer_env_cfg),
    .COV_T(aon_timer_env_cov)
  );
  `uvm_component_utils(aon_timer_virtual_sequencer)

  extern function new (string name = "", uvm_component parent=null);

endclass

function aon_timer_virtual_sequencer::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new
