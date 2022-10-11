// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sleep_pin_retention_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sleep_pin_retention_vseq)

  `uvm_object_new

  import chip_common_pkg::*;

  rand bit [7:0] rounds;

  constraint rounds_c { rounds inside {[8'h 1 : 8'h 7]}; }

  virtual task cpu_init();
    bit [7:0] byte_arr [];
    byte_arr = '{rounds};

    super.cpu_init();

    sw_symbol_backdoor_overwrite("kRounds", byte_arr);

  endtask : cpu_init

  function logic [7:0] sample_gpio();
    // TODO: After https://github.com/lowRISC/opentitan/pull/15339 is merged,
    // revise code to get value from gpio_if not from ios_if.
    logic [7:0] result;

    result = cfg.chip_vif.ios_if.pins_o[IoA7:IoA0];

    return result;
  endfunction : sample_gpio

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // Drive GPIO8 (IoA8) to 0
    cfg.chip_vif.ios_if.drive_pin(IoA8, 1'b 0);

    // GPIO[7:0] to input mode.
    // TODO: After https://github.com/lowRISC/opentitan/pull/15339 is merged,
    // revise code to get value from gpio_if not from ios_if.
    cfg.chip_vif.ios_if.pins_oe[IoA7:IoA0] = '0;

    for (int round = rounds - 1 ; round >= 0 ; round--) begin
      bit   [7:0] gpio_val;
      logic [7:0] gpio_sample;

      string exp_str;
      string printed_log;

      // Init the variables
      printed_log = "";

      // Receive values from SW via sw_logger_vif
      `DV_WAIT(cfg.sw_logger_vif.printed_log == $sformatf("Current Test Round: %1d", round))

      exp_str = "Chosen GPIO value:";

      `DV_SPINWAIT(
          while (printed_log.substr(0, exp_str.len()-1) != exp_str) begin
            @(cfg.sw_logger_vif.printed_log_event);
            printed_log = cfg.sw_logger_vif.printed_log;
          end)

      `DV_CHECK_FATAL(cfg.sw_logger_vif.printed_arg[0] inside {[0:255]})
      gpio_val = cfg.sw_logger_vif.printed_arg[0][7:0];

      `uvm_info(`gfn, $sformatf("Received GPIO value: %2x", gpio_val), UVM_LOW)

      // Check PIN
      gpio_sample = sample_gpio();
      `uvm_info(`gfn,
                $sformatf("Captured GPIO value: %2x", gpio_sample),
                UVM_LOW)
      `DV_CHECK(gpio_sample === gpio_val,
                $sformatf("GPIO value mismatch: Exp[%2x] / Rcv[%2x]",
                          gpio_val, gpio_sample))

      // Wait sleep (normal vs deep)
      `DV_WAIT(cfg.chip_vif.pwrmgr_low_power_if.in_sleep == 1'b 1)
      repeat (5) @(cfg.chip_vif.pwrmgr_low_power_if.cb);

      // Check PIN value
      gpio_sample = sample_gpio();
      `uvm_info(`gfn,
                $sformatf("Captured Retention GPIO value: %2x", gpio_sample),
                UVM_LOW)
      `DV_CHECK((gpio_sample ^ gpio_val) === 'hFF,
                $sformatf("GPIO retention value mismatch: Exp[%2x] / Rcv[%2x]",
                          gpio_val ^ 8'hFF, gpio_sample))

      repeat (5) @(cfg.chip_vif.pwrmgr_low_power_if.cb);

      // Wake up DUT
      cfg.chip_vif.ios_if.drive_pin(IoA8, 1'b 1);
      repeat (3) @(cfg.chip_vif.pwrmgr_low_power_if.cb);
      cfg.chip_vif.ios_if.drive_pin(IoA8, 1'b 0);
    end

  endtask : body

endclass : chip_sw_sleep_pin_retention_vseq
