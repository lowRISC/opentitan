// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_agent extends dv_base_agent #(
  .CFG_T       (entropy_src_xht_agent_cfg),
  .DRIVER_T    (entropy_src_xht_device_driver),
  .SEQUENCER_T (entropy_src_xht_sequencer),
  .MONITOR_T   (entropy_src_xht_monitor),
  .COV_T       (dv_base_agent_cov#(entropy_src_xht_agent_cfg))
);

  `uvm_component_utils(entropy_src_xht_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cfg.has_req_fifo = 1;

    if (!uvm_config_db#(virtual entropy_src_xht_if)::get(
        this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get entropy_src_xht_if handle from uvm_config_db")
    end

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    entropy_src_xht_base_device_seq m_seq
        = entropy_src_xht_base_device_seq::type_id::create("m_seq", this);
    if (cfg.start_default_seq) begin
      uvm_config_db#(uvm_object_wrapper)::set(null, {sequencer.get_full_name(), ".run_phase"},
                                              "default_sequence", m_seq.get_type());
      sequencer.start_phase_sequence(phase);
    end
  endtask

endclass
