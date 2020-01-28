// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class i2c_sanity_vseq extends i2c_rx_tx_vseq;
  `uvm_object_utils(i2c_sanity_vseq)

  `uvm_object_new

  task body();
    do_interrupt = 0;
    i2c_monitor_ctrl(1'b0);
    super.body();

    // init host
    i2c_host_init();
  endtask : body

  task i2c_host_init();
    super.i2c_host_init();
  endtask : i2c_host_init

  task i2c_host_read();
    super.i2c_host_read();
  endtask : i2c_host_read

  task i2c_host_write();
    super.i2c_host_write();
  endtask : i2c_host_write

  task post_start();
    super.post_start();
  endtask : post_start

endclass : i2c_sanity_vseq
