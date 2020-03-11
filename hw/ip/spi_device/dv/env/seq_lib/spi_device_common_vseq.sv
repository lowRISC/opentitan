// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_common_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
