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

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // Drive GPIO8 (IoA8) to 0
    cfg.chip_vif.ios_if.drive_pin(IoA8, 1'b 0);

    for (int round = rounds - 1 ; round >= 0 ; round--) begin
        // TODO: Receive values from SW via sw_logger_vif
        `DV_WAIT(cfg.sw_logger_vif.printed_log == $sformatf("Current Test Round: %1d", round))

        // TODO: Check PIN

        // TODO: Wait sleep (normal vs deep)
        wait(cfg.chip_vif.pwrmgr_low_power_if.in_sleep == 1'b 1);
        repeat (5) @(cfg.chip_vif.pwrmgr_low_power_if.cb);

        // TODO: Check PIN value

        // TODO: Wake up DUT
        cfg.chip_vif.ios_if.drive_pin(IoA8, 1'b 1);
        repeat (3) @(cfg.chip_vif.pwrmgr_low_power_if.cb);
        cfg.chip_vif.ios_if.drive_pin(IoA8, 1'b 0);
    end

  endtask : body

endclass : chip_sw_sleep_pin_retention_vseq
