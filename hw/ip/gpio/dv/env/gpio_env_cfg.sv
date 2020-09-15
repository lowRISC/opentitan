// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_env_cfg extends cip_base_env_cfg #(.RAL_T(gpio_reg_block));

  // flag to indicate if weak pullup has been introduced on gpio
  // By default, weak pull up is always present
  rand bit pullup_en;
  // flag to indicate if weak pulldown has been introduced on gpio
  rand bit pulldown_en;
  // gpio virtual interface
  gpio_vif gpio_vif;

  constraint pullup_pulldown_en_c {
    pullup_en ^ pulldown_en;
  }

  `uvm_object_utils(gpio_env_cfg)
  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // set num_interrupts & num_alerts which will be used to create coverage and more
    num_interrupts = ral.intr_state.get_n_used_bits();

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction : initialize

endclass
