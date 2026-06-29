// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_power_sleep_load_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_power_sleep_load_vseq)

  uint timeout_ns = 1;
  localparam uint CLOCK_PERIOD = 32;

  `uvm_object_new

  virtual task cpu_init;
    bit core_clk_off;
    bit io_clk_off;
    bit usb_slp_clk_off;
    bit usb_act_clk_off;
    bit deep_sleep_on;
    {core_clk_off, io_clk_off, usb_slp_clk_off, usb_act_clk_off, deep_sleep_on} = $urandom();

    super.cpu_init();

    void'($value$plusargs("SW_CORE_CLK_OFF=%d", core_clk_off));
    void'($value$plusargs("SW_IO_CLK_OFF=%d", io_clk_off));
    void'($value$plusargs("SW_USB_SLP_CLK_OFF=%d", usb_slp_clk_off));
    void'($value$plusargs("SW_USB_ACT_CLK_OFF=%d", usb_act_clk_off));
    void'($value$plusargs("SW_DEEP_SLEEP_ON=%d", deep_sleep_on));

    sw_symbol_bkdr_overwr_scalar("kCoreClkOff", core_clk_off);
    sw_symbol_bkdr_overwr_scalar("kIoClkOff", io_clk_off);
    sw_symbol_bkdr_overwr_scalar("kUsbSlpOff", usb_slp_clk_off);
    sw_symbol_bkdr_overwr_scalar("kUsbActOff", usb_act_clk_off);
    sw_symbol_bkdr_overwr_scalar("kDeepSleep", deep_sleep_on);
  endtask

  virtual task body();
    super.body();
    begin : GPIO_CHECK
      // Check IOA2 = 0
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "GPIO active",
               "timeout waiting for SW sync GPIO (1)",
               cfg.sw_test_timeout_ns)
      `DV_WAIT(cfg.chip_vif.gpios_if.pins[2] == '0,
               $sformatf("Timed out waiting for IOA2 == %0h", 0),
               timeout_ns)
      // Check IOA2 = 1
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "all HW is active",
               "timeout waiting for SW sync GPIO (2)",
               cfg.sw_test_timeout_ns)
      `DV_WAIT(cfg.chip_vif.gpios_if.pins[2] == '1,
               $sformatf("Timed out waiting for IOA2 == %0h", 1),
               timeout_ns)
      // Check IOA2 = 0
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "Prepare to exit",
               "timeout waiting for SW sync GPIO (3)",
               cfg.sw_test_timeout_ns)
      `DV_WAIT(cfg.chip_vif.gpios_if.pins[2] == '0,
               $sformatf("Timed out waiting for IOA2 == %0h", 0),
               timeout_ns)
    end : GPIO_CHECK
  endtask : body

  virtual task sw_symbol_bkdr_overwr_scalar(string str, bit [7:0] data);
    bit [7:0] array_data[1] = {data};
    sw_symbol_backdoor_overwrite(str, array_data);
  endtask

endclass : chip_sw_power_sleep_load_vseq
