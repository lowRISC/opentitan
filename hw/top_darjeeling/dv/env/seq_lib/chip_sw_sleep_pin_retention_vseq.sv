// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sleep_pin_retention_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sleep_pin_retention_vseq)
  `uvm_object_new

  localparam int unsigned GpiosTested = 8;    // first 8 GPIOs.
  localparam int unsigned GpioForWakeup = 8;  // 8th GPIO pin used for wakeup.

  rand bit [7:0] rounds;
  constraint rounds_c { rounds inside {[1:7]}; }

  virtual task cpu_init();
    bit [7:0] rounds_byte_arr [] = '{rounds};
    super.cpu_init();
    sw_symbol_backdoor_overwrite("kRounds", rounds_byte_arr);
  endtask : cpu_init

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // Drive wakeup pin to 0.
    cfg.chip_vif.gpios_if.drive_pin(GpioForWakeup, 0);

    // Treat test GPIOs as chip outputs.
    cfg.chip_vif.gpios_if.pins_oe[GpiosTested-1:0] = '0;

    for (int round = rounds - 1 ; round >= 0 ; round--) begin
      logic [GpiosTested-1:0] gpio_exp, gpio_act;

      // Receive values from SW via sw_logger_vif
      `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) ==
               $sformatf("Current Test Round: %1d", round))

      `DV_SPINWAIT(
          string printed_log = "";
          string log = "Chosen GPIO value:";
          while (printed_log.substr(0, log.len() - 1) != log) begin
            @(cfg.sw_logger_vif.printed_log_event);
            printed_log = string'(cfg.sw_logger_vif.printed_log);
          end)

      `DV_CHECK_FATAL(cfg.sw_logger_vif.printed_arg[0] inside {[0:255]})
      gpio_exp = cfg.sw_logger_vif.printed_arg[0][7:0];
      `uvm_info(`gfn, $sformatf("Expected GPIOs value: 0x%0h", gpio_exp), UVM_LOW)

      gpio_act = cfg.chip_vif.gpios_if.pins[GpiosTested-1:0];
      `uvm_info(`gfn, $sformatf("Actual GPIOs value: 0x%0h", gpio_act), UVM_LOW)
      `DV_CHECK(gpio_act === gpio_exp)

      // Wait sleep (normal vs deep)
      `DV_WAIT(cfg.chip_vif.pwrmgr_low_power_if.in_sleep)
      repeat (5) @(cfg.chip_vif.pwrmgr_low_power_if.cb);

      gpio_act = cfg.chip_vif.gpios_if.pins[GpiosTested-1:0];
      `uvm_info(`gfn, $sformatf("Actual GPIOs value during sleep: 0x%0h", gpio_act), UVM_LOW)
      `DV_CHECK((gpio_act ^ gpio_exp) === 'hFF)

      // Wake up DUT
      repeat (5) @(cfg.chip_vif.pwrmgr_low_power_if.cb);
      cfg.chip_vif.gpios_if.drive_pin(GpioForWakeup, 1);
      repeat (3) @(cfg.chip_vif.pwrmgr_low_power_if.cb);
      cfg.chip_vif.gpios_if.drive_pin(GpioForWakeup, 0);
    end
  endtask : body

endclass : chip_sw_sleep_pin_retention_vseq
