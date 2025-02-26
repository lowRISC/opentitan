// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_virtual_sequencer #(type CFG_T = dv_base_env_cfg,
                                  type COV_T = dv_base_env_cov) extends uvm_sequencer;
  `uvm_component_param_utils(dv_base_virtual_sequencer #(CFG_T, COV_T))

  CFG_T         cfg;
  COV_T         cov;

  function new(string name = "dv_base_virtual_sequencer", uvm_component parent);
    super.new(name, parent);
  endfunction

  // Dynamic associative array to store sub-sequencers
  uvm_sequencer_base sub_sequencers[string];

  // Method to dynamically register a sub-sequencer
  function void register_sequencer(string name, uvm_sequencer_base sequencer);
    // Check if the sub_sequencer name does not exists before register it.
    `DV_CHECK_FATAL(!sub_sequencers.exists(name))
    sub_sequencers[name] = sequencer;
  endfunction

  // Method to retrieve a sequencer by name
  function uvm_sequencer_base get_sequencer(string name);
    // Check if the sub_sequencer name is registered before return it.
    `DV_CHECK_FATAL(sub_sequencers.exists(name))
    return sub_sequencers[name];
  endfunction
endclass
