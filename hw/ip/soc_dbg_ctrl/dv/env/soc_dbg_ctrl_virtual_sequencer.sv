// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(soc_dbg_ctrl_env_cfg),
    .COV_T(soc_dbg_ctrl_env_cov)
  );
  `uvm_component_utils(soc_dbg_ctrl_virtual_sequencer)

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
endclass : soc_dbg_ctrl_virtual_sequencer


function soc_dbg_ctrl_virtual_sequencer::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new
