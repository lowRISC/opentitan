// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_env_cfg extends dv_base_env_cfg;

  // ext component cfgs

  `uvm_object_utils_begin(otbn_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new


  virtual function void initialize(bit [31:0] csr_base_addr = '1);
  endfunction

endclass
