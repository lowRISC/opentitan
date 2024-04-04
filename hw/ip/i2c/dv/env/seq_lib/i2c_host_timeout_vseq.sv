// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// timeout test vseq
// this sequence sets timeout enable and value in timeout control reg
// runs random i2c transactions agent is configured to pull down clock
// host will trigger an interrupt stretch timeout when count exceeds the programmed
// value in timeout control reg
class i2c_host_timeout_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_timeout_vseq)
  `uvm_object_new

  // increase num_trans to cover all transaction types
  constraint num_trans_c { num_trans inside {[50 : 100]}; }

  // constraints for i2c timing registers
  constraint t_timeout_c { t_timeout == cfg.seq_cfg.i2c_max_timing; }
  constraint e_timeout_c { e_timeout == 1'b1; }

endclass : i2c_host_timeout_vseq
