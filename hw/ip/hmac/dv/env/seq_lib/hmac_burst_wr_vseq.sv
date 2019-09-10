// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence pre-select certain length within the msg_fifo_length (16 words)
// Wait until msg_fifo has enough depth, then burst write the pre-selected length

class hmac_burst_wr_vseq extends hmac_long_msg_vseq;
  `uvm_object_utils(hmac_burst_wr_vseq)
  `uvm_object_new

  virtual task pre_start();
    do_burst_wr = 1'b1;
    super.pre_start();
  endtask

endclass : hmac_burst_wr_vseq
