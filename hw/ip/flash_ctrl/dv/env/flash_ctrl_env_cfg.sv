// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(flash_ctrl_reg_block));

  // vifs
  mem_bkdr_vif mem_bkdr_vifs[flash_part_e][flash_ctrl_pkg::NumBanks];

  // ext component cfgs
  rand tl_agent_cfg m_eflash_tl_agent_cfg;

  // seq cfg
  flash_ctrl_seq_cfg seq_cfg;

  // knobs
  // ral.status[init_wip] status is set for the very first clock cycle right out of reset.
  // This causes problems in the read value especially in CSR tests.
  int post_reset_delay_clks = 1;

  `uvm_object_utils_begin(flash_ctrl_env_cfg)
    `uvm_field_object(m_eflash_tl_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // create tl agent config obj
    m_eflash_tl_agent_cfg = tl_agent_cfg::type_id::create("m_eflash_tl_agent_cfg");
    m_eflash_tl_agent_cfg.if_mode = dv_utils_pkg::Host;

    // create the seq_cfg
    seq_cfg = flash_ctrl_seq_cfg::type_id::create("seq_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
