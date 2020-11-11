// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class i2c_smoke_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_smoke_vseq)
  `uvm_object_new

  // increase num_trans to cover all transaction types
  constraint num_trans_c { num_trans inside {[50 : 100]}; }

endclass : i2c_smoke_vseq
