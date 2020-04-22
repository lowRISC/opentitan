// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_base_vseq extends cip_base_vseq #(
    .CFG_T               (chip_env_cfg),
    .RAL_T               (chip_reg_block),
    .COV_T               (chip_env_cov),
    .VIRTUAL_SEQUENCER_T (chip_virtual_sequencer)
  );
  `uvm_object_utils(chip_base_vseq)

  // knobs to enable pre_start routines
  bit do_strap_pins_init = 1'b1; // initialize the strap

  // knobs to enable post_start routines

  // various knobs to enable certain routines

  `uvm_object_new

  task post_start();
    do_clear_all_interrupts = 0;
    super.post_start();
  endtask

  virtual task apply_reset(string kind = "HARD");
    // TODO: Cannot assert different types of resets in parallel; due to randomization
    // resets de-assert at different times. If the main rst_n de-asserts before others,
    // the CPU starts executing right away which can cause breakages.
    cfg.m_jtag_agent_cfg.do_trst_n();
    super.apply_reset(kind);
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // Set default frequencies.
    cfg.usb_clk_rst_vif.set_freq_mhz(dv_utils_pkg::ClkFreq48Mhz);
    // Initialize gpio pin default states
    cfg.gpio_vif.set_pulldown_en({chip_env_pkg::NUM_GPIOS{1'b1}});
    // Bring the chip out of reset.
    super.dut_init(reset_kind);
  endtask

  virtual task dut_shutdown();
    // check for pending chip operations and wait for them to complete
    // TODO
  endtask

  virtual task pre_start();
    // Do DUT init after some additional settings.
    bit do_dut_init_save = do_dut_init;
    do_dut_init = 1'b0;
    super.pre_start();
    do_dut_init = do_dut_init_save;

    // Drive strap signals at the start.
    if (do_strap_pins_init) begin
      cfg.srst_n_vif.drive(1'b1);
      cfg.jtag_spi_n_vif.drive(1'b1); // Select JTAG.
      cfg.bootstrap_vif.drive(1'b0);
    end

    // Now safe to do DUT init.
    if (do_dut_init) dut_init();
  endtask

endclass : chip_base_vseq
