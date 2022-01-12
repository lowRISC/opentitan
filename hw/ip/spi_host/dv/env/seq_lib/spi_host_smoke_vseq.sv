// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class spi_host_smoke_vseq extends spi_host_tx_rx_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)
  `uvm_object_new

    int   num_transactions = 2;

  virtual task body();
    fork
      begin: isolation_fork
        fork
          start_reactive_seq();
        join_none

        wait_ready_for_command();
        start_spi_host_trans(num_transactions);
        read_rx_fifo();

        disable fork;
      end
    join
  endtask : body

endclass : spi_host_smoke_vseq
