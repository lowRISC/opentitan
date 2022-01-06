// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_agent extends dv_base_agent #(
  .CFG_T          (key_sideload_agent_cfg),
  .DRIVER_T       (key_sideload_driver),
  .SEQUENCER_T    (key_sideload_sequencer),
  .MONITOR_T      (key_sideload_monitor),
  .COV_T          (key_sideload_agent_cov)
);

  `uvm_component_utils(key_sideload_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get key_sideload_if handle
    if (!uvm_config_db#(virtual key_sideload_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get key_sideload_if handle from uvm_config_db")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    key_sideload_set_seq p_seq;
    if (cfg.start_default_seq) begin
      p_seq = key_sideload_set_seq::type_id::create("p_seq", this);
      forever begin
        `DV_CHECK_RANDOMIZE_FATAL(p_seq)
        p_seq.start(sequencer);
        repeat($urandom_range(10,100)) begin
          @(posedge cfg.vif.clk_i);
        end
      end
    end
  endtask
endclass
