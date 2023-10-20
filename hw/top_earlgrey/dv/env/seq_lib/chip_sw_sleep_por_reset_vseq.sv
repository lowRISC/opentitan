// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sleep_por_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sleep_por_reset_vseq)

  `uvm_object_new

  // This test simply raises a POR via pins, and checks the device exits rom.
  rand int reset_delay;
  constraint reset_delay_c {reset_delay inside {[25 : 40]};}

  virtual task body();
    super.body();
    // mimic external pull up in key in0
    cfg.ast_supply_vif.force_key0_i(1'b1);
    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `uvm_info(`gfn, "In test status", UVM_MEDIUM)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for pad POR")
    // Give the chip enough time to fall asleep.
    //cfg.chip_vif.aon_clk_por_rst_if.wait_clks(10);
    `uvm_info(`gfn, "Flipping POR_N", UVM_MEDIUM)
    execute_reset();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `uvm_info(`gfn, "In test status", UVM_MEDIUM)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Ready for pad POR")
    repeat (30) @cfg.chip_vif.pwrmgr_low_power_if.cb;
    `uvm_info(`gfn, "Flipping sysrst reset", UVM_MEDIUM)
    cfg.ast_supply_vif.pulse_key0_i_next_trigger(reset_delay);
  endtask

  task execute_reset();
    `uvm_info(`gfn, "wait for low power entry", UVM_MEDIUM)
    `DV_WAIT(cfg.chip_vif.pwrmgr_low_power_if.low_power == 1)
    `uvm_info(`gfn, "reset after low power entry", UVM_MEDIUM)
    assert_por_reset_deep_sleep (10);
  endtask // execute_reset

endclass
