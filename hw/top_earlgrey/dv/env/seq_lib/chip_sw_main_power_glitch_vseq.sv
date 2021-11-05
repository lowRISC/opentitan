// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_main_power_glitch_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_main_power_glitch_vseq)

  `uvm_object_new

  rand int cycles_after_trigger;
  constraint cycles_after_trigger_c {cycles_after_trigger inside {[0 : 8]};}

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);

    cfg.ast_supply_vif.glitch_vcmain_supp_i_on_next_trigger(cycles_after_trigger);
  endtask
endclass
