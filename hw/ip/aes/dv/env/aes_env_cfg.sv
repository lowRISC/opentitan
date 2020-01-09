// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_env_cfg extends cip_base_env_cfg #(.RAL_T(aes_reg_block));

  `uvm_object_utils_begin(aes_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize_csr_addr_map_size();
    this.csr_addr_map_size = AES_ADDR_MAP_SIZE;
  endfunction : initialize_csr_addr_map_size

  virtual   function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    super.initialize(csr_base_addr);
  endfunction

endclass
