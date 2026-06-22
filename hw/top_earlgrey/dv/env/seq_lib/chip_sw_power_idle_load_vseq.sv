// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_power_idle_load_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_power_idle_load_vseq)

  uint timeout_ns = 1;
  localparam uint CLOCK_PERIOD = 32;

  `uvm_object_new

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

endclass : chip_sw_power_idle_load_vseq
