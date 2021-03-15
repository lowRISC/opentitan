// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence drives memory accesses during a request to OTP for a new scrambling key,
// and verifies that accesses performed during this time are dropped (handled in scoreboard).
class sram_ctrl_access_during_key_req_vseq extends sram_ctrl_multiple_keys_vseq;

  `uvm_object_utils(sram_ctrl_access_during_key_req_vseq)
  `uvm_object_new

  virtual task pre_start();
    access_during_key_req = 1;
    super.pre_start();
  endtask

endclass
