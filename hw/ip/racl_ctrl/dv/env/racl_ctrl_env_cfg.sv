// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(racl_ctrl_reg_block));

  // ext component cfgs

  `uvm_object_utils_begin(racl_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = racl_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
  endfunction

endclass
