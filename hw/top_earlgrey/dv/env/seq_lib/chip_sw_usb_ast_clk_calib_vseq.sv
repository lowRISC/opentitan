// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_usb_ast_clk_calib_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_usb_ast_clk_calib_vseq)

  `uvm_object_new

  string usbdev_path = {`DV_STRINGIFY(tb.dut.`USBDEV_HIER)};

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
    string idle_det_path = {usbdev_path,
           ".usbdev_impl.u_usb_fs_nb_pe.u_usb_fs_rx.rx_idle_det_o"};

    // See if we can force this at usb_p/usb_n directly later.
    string se0_path = {usbdev_path,
           ".usbdev_impl.u_usbdev_linkstate.line_se0_raw"};

    string link_reset_path = {usbdev_path,
           ".usbdev_impl.u_usbdev_linkstate.link_reset_o"};

    // Force idle to 0 so usbdev does not attempt to suspend.
    `DV_CHECK_FATAL(uvm_hdl_force(idle_det_path, 1'b0));

    // Manipulate single-ended input to create reset event.
    `DV_CHECK_FATAL(uvm_hdl_force(se0_path, 1'b1));

    // Hold reset event until internal state indicates link
    // is reset, then release reset so the link state
    // will advance to Active.
    `DV_SPINWAIT(while (link_reset == 0) begin
                 void'(uvm_hdl_read(link_reset_path, link_reset));
                 cfg.chip_vif.usb_clk_rst_if.wait_clks(10);
                 end,
                  "timeout waiting for link reset",
                 cfg.sw_test_timeout_ns)

    // Release the line.
    `DV_CHECK_FATAL(uvm_hdl_release(se0_path));
  endtask

  virtual task set_usbdev_sof_pulse();
    string sof_path = {usbdev_path,
           ".usbdev_impl.u_usb_fs_nb_pe.sof_valid_o"};

    forever begin
      #(sof_period_us * 1us);
      @(posedge cfg.chip_vif.usb_clk_rst_if.clk);
      `DV_CHECK_FATAL(uvm_hdl_force(sof_path, 1'b1));
      @(posedge cfg.chip_vif.usb_clk_rst_if.clk);
      `DV_CHECK_FATAL(uvm_hdl_release(sof_path));
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
