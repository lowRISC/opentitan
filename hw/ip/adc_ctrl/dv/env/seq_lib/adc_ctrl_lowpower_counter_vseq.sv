// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Check power on/wakeup counters using the assertions in the testbench
// Comprehensively test wakeup_time counter
class adc_ctrl_lowpower_counter_vseq extends adc_ctrl_counter_vseq;

  `uvm_object_utils(adc_ctrl_lowpower_counter_vseq)
  `uvm_object_new

  // Valid values
  constraint testmode_c {testmode inside {AdcCtrlTestmodeLowpower};}

  // Counter values
  constraint counters_c {
    pwrup_time inside {[0 : 2 ** 4 - 1]};
    wakeup_time inside {[100 : 200]};
  }

  virtual task wait_for_txfers();
    wait_all_rx();

    // Wait for a couple of ADC wakeups and make sure that they happen with the configured frequency
    // (the gaps should be the configured wakeup time). This is checked by the WakeupTime_A
    // assertion, which we need to turn on.
    //
    // In case a parent sequence applies a reset, it will kill us too. Fortunately, that happens
    // after the reset has gone through, so we can clean up after ourselves by disabling the
    // assertion (and stopping this sequence) on reset.
    fork begin : isolation_fork
      `DV_ASSERT_CTRL_REQ("WakeupTime_A_CTRL", 1)

      fork
        repeat (2) wait_all_rx();
        cfg.clk_aon_rst_vif.wait_for_reset(.wait_negedge(1'b1), .wait_posedge(1'b0));
      join_any

      `DV_ASSERT_CTRL_REQ("WakeupTime_A_CTRL", 0)
      disable fork;
    end : isolation_fork join
  endtask

endclass : adc_ctrl_lowpower_counter_vseq
