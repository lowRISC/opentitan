// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rram_ctrl_core_reg_block));
  `uvm_object_utils(rram_ctrl_env_cfg)

  // External interfaces
  misc_vif_t misc_vif;

  string host_ral_name = "rram_ctrl_host_reg_block";
  string prim_ral_name = "rram_macro_prim_reg_block";

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void initialize();

endclass : rram_ctrl_env_cfg


function rram_ctrl_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_env_cfg::initialize();
  list_of_alerts = rram_ctrl_env_pkg::LIST_OF_ALERTS;

  ral_model_names.push_back(host_ral_name);
  clk_freqs_mhz[host_ral_name] = clk_freq_mhz;
  ral_model_names.push_back(prim_ral_name);
  clk_freqs_mhz[prim_ral_name] = clk_freq_mhz;

  super.initialize();

  // configure tl agents:
  m_tl_agent_cfg.max_outstanding_req = 1;
  m_tl_agent_cfgs[prim_ral_name].max_outstanding_req = 1;
  // the host interface can tolerate up to 4 outstanding read requests
  m_tl_agent_cfgs[host_ral_name].max_outstanding_req = 4;

  // Set num_interrupts
  begin
    uvm_reg rg = ral.get_reg_by_name("intr_state");
    if (rg != null) begin
      num_interrupts = ral.intr_state.get_n_used_bits();
    end
  end
endfunction : initialize
