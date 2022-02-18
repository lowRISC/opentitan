// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_agent extends dv_base_agent #(
      .CFG_T          (jtag_agent_cfg),
      .DRIVER_T       (jtag_driver),
      .SEQUENCER_T    (jtag_sequencer),
      .MONITOR_T      (jtag_monitor),
      .COV_T          (jtag_agent_cov)
  );

  `uvm_component_utils(jtag_agent)

  // For writing / reading the JTAG DTM registers.
  jtag_dtm_reg_adapter m_jtag_dtm_reg_adapter;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get jtag_if handle
    if (!uvm_config_db#(virtual jtag_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get jtag_if handle from uvm_config_db")
    end
    if (cfg.is_active) begin
      m_jtag_dtm_reg_adapter = jtag_dtm_reg_adapter::type_id::create("m_jtag_dtm_reg_adapter");
      m_jtag_dtm_reg_adapter.cfg = cfg;
    end
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (cfg.is_active) begin
      cfg.jtag_dtm_ral.default_map.set_sequencer(sequencer, m_jtag_dtm_reg_adapter);
    end
  endfunction : end_of_elaboration_phase

endclass
