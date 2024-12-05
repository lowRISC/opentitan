// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_env_cfg extends cip_base_env_cfg #(
  .RAL_T(mbx_core_reg_block)
);
  string mbx_mem_ral_name = "mbx_mem_reg_block";
  string mbx_soc_ral_name = "mbx_soc_reg_block";

  virtual pins_if #(NUM_MAX_INTERRUPTS) intr_soc_vif;

  `uvm_object_utils(mbx_env_cfg)

  function new(string name = "");
    super.new(name);
  endfunction: new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = mbx_env_pkg::LIST_OF_ALERTS;
    // RAL model for the memory TL interface
    ral_model_names.push_back(mbx_mem_ral_name);
    ral_model_names.push_back(mbx_soc_ral_name);

    super.initialize(csr_base_addr);

    // TODO: Revisit the configuration parameters for tl_agent_cfg
    // scxb_mbx_core_cfg
    m_tl_agent_cfgs[mbx_soc_ral_name].max_outstanding_req = 16;
    m_tl_agent_cfgs[mbx_soc_ral_name].if_mode = dv_utils_pkg::Host;

    // agxb_mbx_core_cfg
    m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 16;
    m_tl_agent_cfgs[RAL_T::type_name].if_mode = dv_utils_pkg::Host;

    // mbx_agxb TL I/F
    m_tl_agent_cfgs[mbx_mem_ral_name].max_outstanding_req = 16;
    m_tl_agent_cfgs[mbx_mem_ral_name].if_mode = dv_utils_pkg::Device;

  endfunction: initialize

  virtual function dv_base_reg_block create_ral_by_name(string name);
    if (name == RAL_T::type_name) begin
      return super.create_ral_by_name(name);
    end else if (name == mbx_mem_ral_name) begin
      return mbx_mem_reg_block::type_id::create(mbx_mem_ral_name);
    end else if (name == mbx_soc_ral_name) begin
      return mbx_soc_reg_block::type_id::create(mbx_soc_ral_name);
    end else begin
      `uvm_error(`gfn, $sformatf("%0s is an illegal RAL model name", name))
    end
  endfunction: create_ral_by_name

endclass: mbx_env_cfg
