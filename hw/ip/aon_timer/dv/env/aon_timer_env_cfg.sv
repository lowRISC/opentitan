// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_env_cfg extends cip_base_env_cfg #(.RAL_T(aon_timer_reg_block));

  virtual clk_rst_if        aon_clk_rst_vif;
  virtual pins_if #(1)      lc_escalate_en_vif;
  virtual pins_if #(2)      aon_intr_vif;
  virtual pins_if #(1)      sleep_vif;

  // ext component cfgs

  `uvm_object_utils_begin(aon_timer_env_cfg)
  `uvm_object_utils_end

  function new (string name="");
    super.new(name);

    // The aon_timer RTL doesn't support a devmode input at the moment.
    has_devmode = 1'b0;
  endfunction : new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = aon_timer_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);

    m_tl_agent_cfg.max_outstanding_req = 1;

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();
  endfunction

endclass
