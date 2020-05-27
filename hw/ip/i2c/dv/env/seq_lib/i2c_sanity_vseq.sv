// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class i2c_sanity_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_sanity_vseq)
  `uvm_object_new

  constraint num_wr_bytes_c { num_wr_bytes  inside {[1 : 5]}; }
  constraint num_rd_bytes_c { num_rd_bytes  inside {[1 : 5]}; }
  constraint num_trans_c    { num_trans     inside {100}; }

  task pre_start();
    super.pre_start();
    do_interrupt = 1'b0;
  endtask : pre_start

  task body();
    device_init();
    host_init();

    fork
      while (do_interrupt) process_interrupts();
      host_send_trans(num_trans);
    join
  endtask : body

endclass : i2c_sanity_vseq
