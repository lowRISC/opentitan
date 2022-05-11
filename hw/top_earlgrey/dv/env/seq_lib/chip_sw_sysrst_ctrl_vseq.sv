// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_vseq)

  `uvm_object_new

  rand int cycles_after_trigger;

  constraint cycles_after_trigger_c {cycles_after_trigger inside {[0 : 9]};}

  virtual task body();
    super.body();
    // mimic external pull up in key in0
    cfg.ast_supply_vif.force_key0_i(1'b1);
    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    `uvm_info(`gfn, "SW test ready", UVM_LOW)

    wait (cfg.sw_logger_vif.printed_log == "Reset Request SourceOne is set");
    `uvm_info(`gfn, "SW message delivered to TB", UVM_LOW)
    #1000us;
    `uvm_info(`gfn, "sysrst req set after 1ms", UVM_LOW)
    cfg.ast_supply_vif.pulse_key0_i_next_trigger(50 + cycles_after_trigger);
  endtask

endclass
