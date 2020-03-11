// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_common_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  task pre_start();
    // Common test sequences do not need device init.
    do_usbdev_init = 1'b0;
    super.pre_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
