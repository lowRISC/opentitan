// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence generates back-pressure seq
// The sequence disabled all the rand delay and optional reg checkings

class hmac_back_pressure_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_back_pressure_vseq)

  // Constraints
  extern constraint msg_c;
  extern constraint wr_mask_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task pre_start();
endclass : hmac_back_pressure_vseq


constraint hmac_back_pressure_vseq::msg_c {
  msg.size() dist {
      [129  :999]      :/ 1, // larger than input FIFO depth
      [1000 :3000]     :/ 8, // 1KB - 2KB according to SW immediate usage
      [3001 :10_000]   :/ 1  // temp set to 10KB as max length, spec max size is 2^64 bits
  };
}

constraint hmac_back_pressure_vseq::wr_mask_c {
  $countones(wr_mask) dist {
      TL_DBW       :/ 9,
      [1:TL_DBW-1] :/ 1
  };
}

function hmac_back_pressure_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_back_pressure_vseq::pre_start();
  do_back_pressure = 1'b1;
  super.pre_start();
endtask : pre_start
