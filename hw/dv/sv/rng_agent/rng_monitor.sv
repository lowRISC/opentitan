// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rng_monitor extends dv_base_monitor #(
    .ITEM_T (rng_item),
    .CFG_T  (rng_agent_cfg),
    .COV_T  (rng_agent_cov)
  );
  `uvm_component_utils(rng_monitor)

  // the base class provides the following handles for use:
  // rng_agent_cfg: cfg
  // rng_agent_cov: cov
  // uvm_analysis_port #(rng_item): analysis_port

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
  endtask

endclass
