// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class key_sideload_agent#(
  parameter type KEY_T = keymgr_pkg::hw_key_req_t
) extends dv_base_agent #(
  .CFG_T          (key_sideload_agent_cfg#(KEY_T)),
  .DRIVER_T       (key_sideload_driver#(KEY_T)),
  .SEQUENCER_T    (key_sideload_sequencer#(KEY_T)),
  .MONITOR_T      (key_sideload_monitor#(KEY_T)),
  .COV_T          (key_sideload_agent_cov#(KEY_T))
);

  `uvm_component_utils(key_sideload_agent#(KEY_T))

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get key_sideload_if handle
    if (!uvm_config_db#(virtual key_sideload_if#(KEY_T))::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get key_sideload_if handle from uvm_config_db")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    key_sideload_set_seq#(KEY_T) p_seq;
    if (cfg.start_default_seq) begin
      p_seq = key_sideload_set_seq#(KEY_T)::type_id::create("p_seq", this);
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
