// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Check power on/wakeup counters using the assertions in the testbench
// Comprehensively test wakeup_time counter
class adc_ctrl_lowpower_counter_vseq extends adc_ctrl_counter_vseq;

  `uvm_object_utils(adc_ctrl_lowpower_counter_vseq)
  `uvm_object_new

  // Valid values
  constraint testmode_c {testmode inside {AdcCtrlLowpower};}

  // Counter values
  constraint counters_c {
    pwrup_time inside {[0 : 2 ** 4 - 1]};
    wakeup_time inside {[100 : 200]};
  }

  virtual task wait_for_txfers();
    wait_all_rx();
    `DV_ASSERT_CTRL_REQ("WakeupTime_A_CTRL", 1)
    wait_all_rx();
    wait_all_rx();
    `DV_ASSERT_CTRL_REQ("WakeupTime_A_CTRL", 0)
  endtask

endclass : adc_ctrl_lowpower_counter_vseq
