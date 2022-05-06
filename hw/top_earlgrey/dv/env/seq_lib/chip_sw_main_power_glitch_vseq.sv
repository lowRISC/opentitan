// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_main_power_glitch_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_main_power_glitch_vseq)

  `uvm_object_new

  rand int cycles_after_trigger;
  constraint cycles_after_trigger_c {cycles_after_trigger inside {[0 : 8]};}

  virtual task pre_start();
    super.pre_start();
    //expect_fatal_alerts = 1;
    //cfg.scoreboard.set_exp_alert("pwrmgr_aon_fatal_fault", .is_fatal(1'b1), .max_delay(500000));
    // disable expected assertion error for power glitch test
    $assertoff(0,"pwrmgr_ast_sva_if");
    $assertoff(1,"tb.dut.top_earlgrey.pwrmgr_rstmgr_sva_if.MainPwrRstOff_A");
    $assertoff(1,"tb.dut.top_earlgrey.pwrmgr_rstmgr_sva_if.MainPwrRstOn_A");
  endtask

  virtual task body();
    super.body();
    cfg.scoreboard.do_alert_check = 0;

    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);
    cfg.ast_supply_vif.glitch_vcmain_pok_on_next_trigger(cycles_after_trigger);

    $display("JDONDBG st1");
    // the above glitch should cause the system to reboot, now wait for reset
    // before re-enabling assertion
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom);
    cfg.ast_supply_vif.reenable_vcmain_assertion();

    $display("JDONDBG st2");
  endtask
endclass
