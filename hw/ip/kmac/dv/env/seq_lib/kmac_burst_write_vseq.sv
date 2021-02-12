// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_burst_write_vseq extends kmac_long_msg_and_output_vseq;

  `uvm_object_utils(kmac_burst_write_vseq)
  `uvm_object_new

  virtual task pre_start();
    burst_write = 1;
    super.pre_start();
  endtask

endclass
