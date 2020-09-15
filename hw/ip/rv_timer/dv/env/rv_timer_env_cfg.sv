// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_timer_env_cfg extends cip_base_env_cfg #(.RAL_T(rv_timer_reg_block));
  `uvm_object_utils(rv_timer_env_cfg)
  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    // set num_interrupts
    num_interrupts = NUM_HARTS * NUM_TIMERS;

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

endclass
