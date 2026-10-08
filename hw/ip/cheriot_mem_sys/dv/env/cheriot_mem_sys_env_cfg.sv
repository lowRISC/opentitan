// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cheriot_mem_sys_env_cfg extends cip_base_env_cfg #(.RAL_T(cheriot_mem_sys_regs_reg_block));

  // ext component cfgs

  `uvm_object_utils_begin(cheriot_mem_sys_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit inherit_ral_models = 1'b0);
    list_of_alerts = cheriot_mem_sys_env_pkg::LIST_OF_ALERTS;
    super.initialize(inherit_ral_models);
    num_interrupts = ral.intr_state.get_n_used_bits();
  endfunction

endclass
