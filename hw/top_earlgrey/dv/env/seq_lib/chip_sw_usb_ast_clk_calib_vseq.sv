// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_usb_ast_clk_calib_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_usb_ast_clk_calib_vseq)

  `uvm_object_new

  int sof_period_us;

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] sof_period_us_data[];
    super.cpu_init();

    if ( !$value$plusargs("usb_fast_sof=%0d", sof_period_us) ) begin
      sof_period_us = 1000;
    end else begin
      sof_period_us = 20;
    end

    sof_period_us_data = {<<byte{sof_period_us}};
    sw_symbol_backdoor_overwrite("kSoFPeriodUs", sof_period_us_data);
  endtask

  virtual task connect_usbdev();
    int link_reset = 0;

    // Force idle to 0 so usbdev does not attempt to suspend.
    void'(cfg.chip_vif.signal_probe_usbdev_rx_idle_det_o(SignalProbeForce, 0));

    // Manipulate single-ended input to create reset event.
    // TODO: See if we can force this at usb_p/usb_n directly later.
    void'(cfg.chip_vif.signal_probe_usbdev_se0(SignalProbeForce, 1));

    // Hold reset event until internal state indicates link
    // is reset, then release reset so the link state
    // will advance to Active.
    `DV_SPINWAIT(
        while (link_reset == 0) begin
          link_reset = cfg.chip_vif.signal_probe_usbdev_link_reset_o(SignalProbeSample);
          cfg.chip_vif.usb_clk_rst_if.wait_clks(10);
        end,
        "timeout waiting for link reset",
        cfg.sw_test_timeout_ns)

    // Release the line.
    void'(cfg.chip_vif.signal_probe_usbdev_se0(SignalProbeRelease));
  endtask

  virtual task set_usbdev_sof_pulse();
    forever begin
      #(sof_period_us * 1us);
      cfg.chip_vif.usb_clk_rst_if.wait_clks(1);
      void'(cfg.chip_vif.signal_probe_usbdev_sof_valid_o(SignalProbeForce, 1));
      cfg.chip_vif.usb_clk_rst_if.wait_clks(1);
      void'(cfg.chip_vif.signal_probe_usbdev_sof_valid_o(SignalProbeRelease));
    end
  endtask

  virtual task body();
    super.body();

    // Wait for software synchronization.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Enable usb");,
                 "timeout waiting for C side trigger",
                 cfg.sw_test_timeout_ns)
     connect_usbdev();

    // Wait for software synchronization.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "Wait for sof to calibrate clocks");,
                 "timeout waiting for C side trigger",
                 cfg.sw_test_timeout_ns)

    // Spawn off a thread to continously create sof pulses.
    fork set_usbdev_sof_pulse(); join_none

    // Wait for software sychronization.
    `DV_SPINWAIT(wait(cfg.sw_logger_vif.printed_log == "sof complete");,
             "timeout waiting for C side completion",
             cfg.sw_test_timeout_ns)
  endtask

endclass : chip_sw_usb_ast_clk_calib_vseq
