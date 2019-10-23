// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_env_cfg extends cip_base_env_cfg #(.RAL_T(aes_reg_block));

  // ext component cfgs

  `uvm_object_utils_begin(aes_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new


    string name = "aes_config_object";
    
  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1,
                                   bit [TL_AW-1:0] csr_addr_map_size = ADDR_MAP_SIZE);
    super.initialize(csr_base_addr, csr_addr_map_size);

    // set num_interrupts & num_alerts which will be used to create coverage and more
  //  num_interrupts = ral.intr_state.get_n_used_bits();
  //  num_alerts = 0;
  endfunction

endclass
