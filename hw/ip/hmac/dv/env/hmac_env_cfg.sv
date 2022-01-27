// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_env_cfg extends cip_base_env_cfg #(.RAL_T(hmac_reg_block));

  // A flag to nofity scoreboard if digest is corrupted by wipe_secret command.
  bit wipe_secret_triggered;

  // Flag to notify stress_all_with_rand_reset task that hash_process command is triggered.
  // This would help trying to issue reset at specific timing during hmac hashing.
  bit hash_process_triggered;

  `uvm_object_utils(hmac_env_cfg)
  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = hmac_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // set num_interrupts & num_alerts which will be used to create coverage and more
    num_interrupts = ral.intr_state.get_n_used_bits();

    // only support 2 outstanding TL items in tlul_adapter
    m_tl_agent_cfg.max_outstanding_req = 2;
  endfunction

endclass
