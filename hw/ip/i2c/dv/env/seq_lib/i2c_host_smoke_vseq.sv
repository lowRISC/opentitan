// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic smoke test vseq
class i2c_host_smoke_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_host_smoke_vseq)
  `uvm_object_new

  // increase num_trans to cover all transaction types
  constraint num_trans_c { num_trans inside {[50 : 100]}; }

  virtual task body();
    bit do_interrupt = 1'b1;
    initialization();
    `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
    fork
      begin
        while (!cfg.under_reset && do_interrupt) process_interrupts();
      end
      begin
        host_send_trans(.max_trans(num_trans),
                        .trans_type(ReadOnly),
                        .read(1));
        do_interrupt = 1'b0; // gracefully stop process_interrupts
      end
    join
    `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
  endtask : body


endclass : i2c_host_smoke_vseq
