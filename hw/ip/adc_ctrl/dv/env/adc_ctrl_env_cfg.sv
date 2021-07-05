// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_env_cfg extends cip_base_env_cfg #(
  .RAL_T(adc_ctrl_reg_block)
);

  virtual clk_rst_if clk_aon_rst_vif;

  // ext component cfgs

  `uvm_object_utils_begin(adc_ctrl_env_cfg)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [31:0] csr_base_addr = '1);
    list_of_alerts = adc_ctrl_env_pkg::LIST_OF_ALERTS;
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
