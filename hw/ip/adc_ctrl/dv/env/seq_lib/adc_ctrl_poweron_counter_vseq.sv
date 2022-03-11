// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Check power on/wakeup counters using the assertions in the testbench
// Comprehensively test pwrup_time counter
class adc_ctrl_poweron_counter_vseq extends adc_ctrl_counter_vseq;

  `uvm_object_utils(adc_ctrl_poweron_counter_vseq)
  `uvm_object_new

  // Valid values
  constraint testmode_c {testmode inside {AdcCtrlTestmodeOneShot, AdcCtrlTestmodeNormal};}

endclass : adc_ctrl_poweron_counter_vseq
