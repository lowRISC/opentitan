// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_env_cfg extends cip_base_env_cfg #(.RAL_T(${name}_reg_block));
% elif has_ral:
class ${name}_env_cfg extends dv_base_env_cfg #(.RAL_T(${name}_reg_block));
% else:
class ${name}_env_cfg extends dv_base_env_cfg;
% endif

  // ext component cfgs
% for agent in env_agents:
  rand ${agent}_agent_cfg m_${agent}_agent_cfg;
% endfor

  `uvm_object_utils_begin(${name}_env_cfg)
% for agent in env_agents:
    `uvm_field_object(m_${agent}_agent_cfg, UVM_DEFAULT)
% endfor
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
% if has_alerts:
    list_of_alerts = ${name}_env_pkg::LIST_OF_ALERTS;
% endif
% if has_edn:
    cfg.has_edn = 1;
% endif
% if has_ral:
    super.initialize(csr_base_addr);
% endif
% for agent in env_agents:
    // create ${agent} agent config obj
    m_${agent}_agent_cfg = ${agent}_agent_cfg::type_id::create("m_${agent}_agent_cfg");
% endfor
% if has_interrupts:

    // set num_interrupts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
% endif
  endfunction

endclass
