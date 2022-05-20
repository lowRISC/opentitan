// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_pwrmgr_random_sleep_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_pwrmgr_random_sleep_vseq)
  `uvm_object_new

  rand bit[7:0] assa[3];
  constraint assa_c {
    foreach (assa[i]) assa[i] inside {[0:1]};
  }

  virtual task cpu_init();
    super.cpu_init();
    sw_symbol_backdoor_overwrite("ASSA", assa);
  endtask // cpu_init

endclass
