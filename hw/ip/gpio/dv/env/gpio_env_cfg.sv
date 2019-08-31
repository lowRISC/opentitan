// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_env_cfg extends cip_base_env_cfg #(.RAL_T(gpio_reg_block));

  bit      active_high_pullup = 1'b1;
  gpio_vif gpio_vif;

  `uvm_object_utils(gpio_env_cfg)

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1,
                                   bit [TL_AW-1:0] csr_addr_map_size = 2048);
    super.initialize();
    // TODO-Remove plusarg check from here, as it is already
    // checked from tb module
    if ($value$plusargs("active_high_pullup=%0b", active_high_pullup)) begin
      `uvm_info(`gfn, $sformatf("active_high_pullup plusarg value = %0b", active_high_pullup),
                UVM_HIGH)
    end
    // set num_interrupts & num_alerts which will be used to create coverage and more
    num_interrupts = ral.intr_state.get_n_used_bits();
  endfunction

endclass
