// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_monitor #(type ITEM_T = uvm_sequence_item,
                        type CFG_T  = dv_base_agent_cfg,
                        type COV_T  = dv_base_agent_cov) extends uvm_monitor;
  `uvm_component_param_utils(dv_base_monitor #(ITEM_T, CFG_T, COV_T))

  CFG_T cfg;
  COV_T cov;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(ITEM_T) analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_port = new("analysis_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    fork
      collect_trans(phase);
    join
  endtask

  // collect transactions forever
  virtual protected task collect_trans(uvm_phase phase);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

endclass

