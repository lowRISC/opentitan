// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Custom intr_test with the intent of hitting cross-coverage for intr_test/intr_state/enables
class aon_timer_custom_intr_vseq extends aon_timer_base_vseq;
  `uvm_object_utils(aon_timer_custom_intr_vseq)

  rand bit wdog_enable, wkup_enable;
  rand bit [1:0] intr_test_value;

  extern constraint intr_test_c;

  extern function new (string name="");
  extern task intr_stimulus();
  extern task body();
endclass : aon_timer_custom_intr_vseq

constraint aon_timer_custom_intr_vseq::intr_test_c {
  intr_test_value != 0;
}

function aon_timer_custom_intr_vseq::new (string name="");
  super.new(name);
endfunction : new

task aon_timer_custom_intr_vseq::intr_stimulus();
  bit [1:0] read_intr_state;
  // Write random value to the wkup_ctrl/wdog_ctrl and intr_test registers
  cfg.aon_clk_rst_vif.wait_clks_or_rst(1);

  `uvm_info(`gfn, $sformatf("Setting CTRL registers with enables for WKUP=0x%0x/WDOG=0x%0x",
                            wkup_enable, wdog_enable), UVM_DEBUG)
  csr_utils_pkg::csr_wr(ral.wdog_ctrl.enable, wdog_enable);
  csr_utils_pkg::csr_wr(ral.wkup_ctrl.enable, wkup_enable);

  `uvm_info(`gfn, $sformatf("Write: Test_intr=0x%0x",intr_test_value), UVM_DEBUG)
  csr_utils_pkg::csr_wr(ral.intr_test, intr_test_value);
  csr_utils_pkg::csr_rd(ral.intr_state, read_intr_state);
  cfg.aon_clk_rst_vif.wait_clks_or_rst(5);
endtask : intr_stimulus

task aon_timer_custom_intr_vseq::body();
  aon_timer_init();
  intr_stimulus();
  aon_timer_shutdown();
endtask : body
