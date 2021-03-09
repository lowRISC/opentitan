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

  // Local queue for holding received UART TX data.
  byte uart_tx_data_q[$];

  `uvm_object_new

  task post_start();
    do_clear_all_interrupts = 0;
    super.post_start();
  endtask

  virtual task apply_reset(string kind = "HARD");
    // Note: The JTAG reset does not have a dedicated pad and is muxed with other chip IOs.
    // These IOs have pad attributes that are driven from registers, and as long as
    // the reset line of those registers is X, the registers and hence the pad outputs
    // will also be X. This causes the JTAG reset to not properly propagate, and hence we
    // have to assert the main reset before that (release can happen in a randomized way
    // via the apply_reset task later on).
    cfg.clk_rst_vif.drive_rst_pin(1'b0);
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
    // Initialize flash seeds
    cfg.flash_info0_bkdr_vif.set_mem();
    cfg.flash_info1_bkdr_vif.set_mem();
    // Backdoor load the OTP image.
    cfg.otp_bkdr_vif.load_mem_from_file({cfg.sw_images[SwTypeOtp], ".vmem"});
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
      cfg.bootstrap_vif.drive(cfg.use_spi_load_bootstrap);
    end

    // Now safe to do DUT init.
    if (do_dut_init) dut_init();
  endtask

  // Grab packets sent by the DUT over the UART TX port.
  virtual task get_uart_tx_items();
    uart_item item;
    forever begin
      p_sequencer.uart_tx_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received UART data over TX:\n%0h", item.data), UVM_HIGH)
      uart_tx_data_q.push_back(item.data);
    end
  endtask

endclass : chip_base_vseq
