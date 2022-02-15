// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_env_cfg extends cip_base_env_cfg #(.RAL_T(rv_dm_regs_reg_block));

  // ext component cfgs
  virtual rv_dm_if    rv_dm_vif;
  rand jtag_agent_cfg m_jtag_agent_cfg;
  rand tl_agent_cfg   m_tl_sba_agent_cfg;

  // A constant that can be referenced from anywhere.
  string rom_ral_name = "rv_dm_debug_mem_reg_block";

  `uvm_object_utils_begin(rv_dm_env_cfg)
    `uvm_field_object(m_jtag_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(m_tl_sba_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = rv_dm_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_fault";

    // Set up second RAL model for ROM memory and associated collateral
    ral_model_names.push_back(rom_ral_name);

    // both RAL models use same clock frequency
    clk_freqs_mhz["rv_dm_debug_mem_reg_block"] = clk_freq_mhz;

    super.initialize(csr_base_addr);
    `uvm_info(`gfn, $sformatf("ral_model_names: %0p", ral_model_names), UVM_LOW)

    // Both, the regs and the debug mem TL device (in the DUT) only support 1 outstanding.
    m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 1;
    m_tl_agent_cfgs[rom_ral_name].max_outstanding_req = 1;

    // Create jtag agent config obj
    m_jtag_agent_cfg = jtag_agent_cfg::type_id::create("m_jtag_agent_cfg");
    m_jtag_agent_cfg.if_mode = dv_utils_pkg::Host;
    m_jtag_agent_cfg.is_active = 1'b1;

    // Create TL agent config obj for the SBA port.
    m_tl_sba_agent_cfg =  tl_agent_cfg::type_id::create("m_tl_sba_agent_cfg");
    m_tl_sba_agent_cfg.if_mode = dv_utils_pkg::Device;
    m_tl_sba_agent_cfg.is_active = 1'b1;
  endfunction

  protected virtual function void post_build_ral_settings(dv_base_reg_block ral);
    // The backdoor HDL paths are set incorrectly on the debug mem RAL structures by the reggen
    // tool. We just remove all HDL paths and skip backdoor writes entirely.
    // TODO: Enable backdoor writes later.
    if (ral.get_name() == rom_ral_name) begin
      rv_dm_debug_mem_reg_block debug_mem_ral;
      uvm_reg regs[$];

      ral.get_registers(regs);
      foreach (regs[i]) begin
        regs[i].clear_hdl_path("ALL");
      end

      // ROM within debug mem supports partial accesses, but strangely, the TL adapter does not
      // allow byte accesses. See #10765.
      `downcast(debug_mem_ral, ral)
      debug_mem_ral.rom.set_mem_partial_write_support(1);

      // ROM within the debug mem is RO - it ignores writes instead of throwing an error response.
      debug_mem_ral.rom.set_write_to_ro_mem_ok(1);

      // TODO(#10837): Accesses to unmapped regions of debug mem RAL space does not return an error
      // response. Fix this if design is updated.
      debug_mem_ral.set_unmapped_access_ok(1);

      //TODO(#10765): We don't support byte writes at this time.
      debug_mem_ral.set_support_byte_enable(1'b0);
    end
  endfunction

endclass
