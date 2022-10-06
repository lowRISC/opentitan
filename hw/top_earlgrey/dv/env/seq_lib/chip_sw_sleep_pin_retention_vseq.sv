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

    for (int unsigned round = 0 ; round < rounds ; round++) begin
        // TODO: Receive values from SW via sw_logger_vif

        // TODO: Check PIN

        // TODO: Wait sleep (normal vs deep)

        // TODO: Check PIN value

        // TODO: Wake up DUT
    end

  endtask : body

endclass : chip_sw_sleep_pin_retention_vseq
