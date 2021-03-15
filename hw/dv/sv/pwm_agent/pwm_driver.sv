// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_driver extends dv_base_driver #(.ITEM_T(pwm_item),
                                          .CFG_T (pwm_agent_cfg));
  `uvm_component_utils(pwm_driver)
  `uvm_component_new

  virtual task reset_signals();
    forever begin
      @(negedge cfg.vif.rst_core_n);
      `uvm_info(`gfn, "\ndriver in reset progress", UVM_DEBUG)
      @(posedge cfg.vif.rst_core_n);
      `uvm_info(`gfn, "\ndriver out of reset", UVM_DEBUG)
    end
  endtask : reset_signals

  virtual task get_and_drive();
    @(posedge cfg.vif.rst_core_n);
    // pwm does not require responses from pwm_agent thus this task is kept to a minimum
    forever begin
      #1us;
    end
  endtask : get_and_drive

endclass
