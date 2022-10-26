// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_main_power_glitch_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_main_power_glitch_vseq)

  `uvm_object_new

  // Cycles to wait for the pwrmgr to start normal sleep processing after trigger.
  rand int cycles_after_trigger;
  constraint cycles_after_trigger_c {cycles_after_trigger inside {[5 : 13]};}

  virtual task pre_start();
    super.pre_start();
    // disable expected assertion error for power glitch test
    $assertoff(1,"tb.dut.top_earlgrey.pwrmgr_rstmgr_sva_if.MainPwrRstOff_A");
    $assertoff(1,"tb.dut.top_earlgrey.pwrmgr_rstmgr_sva_if.MainPwrRstOn_A");
  endtask

  virtual task body();
    super.body();
    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    cfg.ast_supply_vif.glitch_vcmain_pok_on_next_core_sleeping_trigger(cycles_after_trigger);

    // the above glitch should cause the system to reboot, now wait for reset
    // before re-enabling assertion
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
    cfg.ast_supply_vif.reenable_vcmain_assertion();
  endtask
endclass
