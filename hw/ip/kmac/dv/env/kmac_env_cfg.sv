// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_env_cfg extends cip_base_env_cfg #(.RAL_T(kmac_reg_block));

  // ext interfaces
  idle_vif        idle_vif;
  sideload_vif    sideload_vif;

  // Masked KMAC is the default configuration
  bit enable_masking = 1;

  `uvm_object_utils_begin(kmac_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    has_edn = 1;
    super.initialize(csr_base_addr);

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction

endclass
