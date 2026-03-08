// Copyright lowRISC contributors (OpenTitan project).
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

    // Get jtag_if handle and jtag_mon_if handle if they haven't already been supplied. The
    // jtag_mon_if handle is optional.
    if (cfg.vif == null && !uvm_config_db#(virtual jtag_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get jtag_if handle from uvm_config_db")
    end
    if (cfg.mon_vif == null) begin
      void'(uvm_config_db#(virtual jtag_mon_if)::get(this, "", "mon_vif", cfg.mon_vif));
    end

    if (cfg.is_active) begin
      m_jtag_dtm_reg_adapter = jtag_dtm_reg_adapter::type_id::create("m_jtag_dtm_reg_adapter");
      m_jtag_dtm_reg_adapter.set_ir_len(cfg.ir_len);
    end
  endfunction

  // Pass a handle to a uvm_reg_map that represents the DTM registers. See jtag_dtm_reg_adapter for
  // a more detailed description of what this does.
  function void set_reg_map(uvm_reg_map reg_map);
    if (m_jtag_dtm_reg_adapter == null) begin
      `uvm_fatal(get_full_name(), "No reg adapter: is the agent not active?")
    end
    m_jtag_dtm_reg_adapter.set_reg_map(reg_map);
  endfunction

endclass
