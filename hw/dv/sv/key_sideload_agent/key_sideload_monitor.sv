// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_monitor #(
    parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends dv_base_monitor #(
    .ITEM_T (key_sideload_item#(KEY_T)),
    .CFG_T  (key_sideload_agent_cfg#(KEY_T)),
    .COV_T  (key_sideload_agent_cov#(KEY_T))
  );
  `uvm_component_utils(key_sideload_monitor#(KEY_T))

  // the base class provides the following handles for use:
  // key_sideload_agent_cfg: cfg
  // key_sideload_agent_cov: cov
  // uvm_analysis_port #(key_sideload_item): analysis_port

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans();
    key_sideload_item#(KEY_T) prev_item;
    key_sideload_item#(KEY_T) curr_item;
    prev_item = key_sideload_item#(KEY_T)::type_id::create("prev_item");
    curr_item = key_sideload_item#(KEY_T)::type_id::create("curr_item");
    forever begin
      @(posedge cfg.vif.clk_i or negedge cfg.vif.rst_ni);
      if (!cfg.vif.rst_ni) continue;
      curr_item.valid = cfg.vif.sideload_key.valid;
      curr_item.key0  = cfg.vif.sideload_key.key[0];
      curr_item.key1  = cfg.vif.sideload_key.key[1];
      if ((prev_item.valid != curr_item.valid) || (prev_item.key0 != curr_item.key0) ||
         (prev_item.key1 != curr_item.key1)) begin
        analysis_port.write(curr_item);
        prev_item.copy(curr_item);
      end
    end
  endtask

endclass
