// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test causes the rstmgr's por_n_i to be asserted, both due to AON power glitches and to the
// chip's POR_N input. These resets are sent at random delays.
class chip_sw_full_aon_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_full_aon_reset_vseq)

  `uvm_object_new

  // We don't use num_iterations since that causes waiting for test_main to complete that number of
  // times, but it is better to send the various resets while the chip is initializing.
  localparam int NumberOfResets = 8;

  typedef enum bit {
    ResetCauseGlitch,
    ResetCausePin
  } reset_cause_e;
  rand reset_cause_e reset_cause;

  rand int cycles_before_trigger;
  constraint cycles_before_trigger_c {cycles_before_trigger inside {[10 : 50]};}

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom);

    repeat (NumberOfResets) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      if (reset_cause == ResetCausePin) begin
        apply_reset();
      end else begin
        cfg.ast_supply_vif.glitch_vcaon_pok(0);
      end
      cfg.sw_test_status_vif.sw_test_status = SwTestStatusUnderReset;
      repeat (cycles_before_trigger) @(posedge cfg.ast_supply_vif.clk);
    end
  endtask
endclass
