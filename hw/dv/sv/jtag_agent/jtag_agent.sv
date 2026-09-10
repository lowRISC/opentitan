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

  // Connect the agent to a uvm_reg_map that represents the DTM registers.
  //
  // The connection teaches reg_map to use this agent's sequencer when generating register accesses.
  // It also teaches this register adapter how to pick sensible DR values for register reads. See
  // jtag_dtm_reg_adapter::set_reg_map and jtag_dtm_reg_adapter::get_wdata_for_read for more
  // information.
  function void set_reg_map(uvm_reg_map reg_map);
    if (m_jtag_dtm_reg_adapter == null) begin
      `uvm_fatal(get_full_name(),
                 "No reg adapter. This must be run after the build phase on an active agent.")
    end
    m_jtag_dtm_reg_adapter.set_reg_map(reg_map);
    reg_map.set_sequencer(sequencer, m_jtag_dtm_reg_adapter);
  endfunction

endclass
