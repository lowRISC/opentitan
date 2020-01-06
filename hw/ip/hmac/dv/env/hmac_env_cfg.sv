// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_env_cfg extends cip_base_env_cfg #(.RAL_T(hmac_reg_block));

  `uvm_object_utils(hmac_env_cfg)
  `uvm_object_new

  virtual function void initialize_csr_addr_map_size();
    this.csr_addr_map_size = HMAC_ADDR_MAP_SIZE;
  endfunction : initialize_csr_addr_map_size

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
    en_mem_byte_write   = 1;
    en_mem_read         = 0;
    mem_ranges.push_back('{HMAC_MSG_FIFO_BASE, HMAC_MSG_FIFO_LAST_ADDR});
    list_of_alerts      = {"msg_push_sha_disabled"};
  endfunction

  // ral flow is limited in terms of setting correct field access policies and reset values
  // We apply those fixes here - please note these fixes need to be reflected in the scoreboard
  protected virtual function void apply_ral_fixes();
    // fix access policies
    // fix reset values for fields with "hwext" attribute set
    ral.status.fifo_empty.set_reset(1'b1);
    // set num_interrupts & num_alerts which will be used to create coverage and more
    num_interrupts = ral.intr_state.get_n_used_bits();
  endfunction

endclass
