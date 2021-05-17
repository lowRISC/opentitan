// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// --------------------
// Device sequence
// --------------------
class spi_device_seq extends spi_base_seq;

  `uvm_object_utils(spi_device_seq)
  `uvm_object_new

  spi_item req_q[$];

  virtual task body();
    fork
      forever begin
        spi_item req;
        p_sequencer.req_analysis_fifo.get(req);
        req_q.push_back(req);
      end
      forever begin
        spi_item rsp;
        wait(req_q.size > 0);
        rsp = req_q.pop_front();
        start_item(rsp);
        finish_item(rsp);
      end
    join
  endtask : body

endclass : spi_device_seq
