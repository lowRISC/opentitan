// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates back-pressure seq
// The sequence disabled all the rand delay and optional reg checkings

class hmac_back_pressure_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_back_pressure_vseq)
  `uvm_object_new

  constraint msg_c {
    msg.size() dist {
        [65  :999]    :/ 1,
        [1000:3000]   :/ 8, // 1KB - 2KB according to SW immediate usage
        [3001:10_000] :/ 1  // temp set to 10KB as max length, spec max size is 2^64 bits
    };
  }
  constraint wr_mask_c {
    $countones(wr_mask) dist {
        TL_DBW       :/ 9,
        [1:TL_DBW-1] :/ 1
    };
  }

  virtual task pre_start();
    do_back_pressure = 1'b1;
    super.pre_start();
  endtask

endclass : hmac_back_pressure_vseq
