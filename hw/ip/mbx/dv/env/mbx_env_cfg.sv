// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_env_cfg extends cip_base_env_cfg #(
  .RAL_T(mbx_core_reg_block)
);
  // RoT-side SRAM interface.
  tl_agent_cfg m_tl_agent_sram_cfg;

  // TODO: change identifier and probably lose the RAL name since the notion of
  // a RAL makes no sense.
  string mbx_mem_ral_name = "mbx_mem_reg_block";
  // SoC-side configuration registers.
  string mbx_soc_ral_name = "mbx_soc_reg_block";

  virtual pins_if #(NUM_MAX_INTERRUPTS) intr_soc_vif;

  `uvm_object_utils_begin(mbx_env_cfg)
    `uvm_field_object(m_tl_agent_sram_cfg, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = mbx_env_pkg::LIST_OF_ALERTS;

    // RAL for the SoC-side register interface.
    ral_model_names.push_back(mbx_soc_ral_name);

    super.initialize(csr_base_addr);

    // Interrupt count
    num_interrupts = ral.intr_state.get_n_used_bits();

    // TODO: Revisit the configuration parameters for tl_agent_cfg
    // RoT-side configuration registers.
    m_tl_agent_cfgs[RAL_T::type_name].max_outstanding_req = 16;
    m_tl_agent_cfgs[RAL_T::type_name].if_mode = dv_utils_pkg::Host;

    // SoC-side configuration registers.
    m_tl_agent_cfgs[mbx_soc_ral_name].max_outstanding_req = 16;
    m_tl_agent_cfgs[mbx_soc_ral_name].if_mode = dv_utils_pkg::Host;

    // RoT-side SRAM interface. This has no RAL because it is a Device-mode TL agent
    // and thus we manage the agent and its configuration ourselves.
    `uvm_create_obj(tl_agent_cfg, m_tl_agent_sram_cfg)
    // The DUT logic will send up to 4 overlapped read/write requests, which it counts
    // internally.
    m_tl_agent_sram_cfg.max_outstanding_req = 4;
    m_tl_agent_sram_cfg.if_mode = dv_utils_pkg::Device;

    // The mailbox must be able to handle combinational devices too, i.e. those
    // with a combinational path from `a_valid` to `d_valid` on the TL-UL bus.
    m_tl_agent_sram_cfg.device_can_rsp_on_same_cycle = 1'b1;

  endfunction: initialize

  virtual protected function dv_base_reg_block create_ral_by_name(string name);
    if (name == RAL_T::type_name) begin
      return super.create_ral_by_name(name);
    end else if (name == mbx_soc_ral_name) begin
      return mbx_soc_reg_block::type_id::create(mbx_soc_ral_name);
    end else begin
      `uvm_error(`gfn, $sformatf("%0s is an illegal RAL model name", name))
    end
  endfunction: create_ral_by_name

endclass: mbx_env_cfg
