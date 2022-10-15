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
      get_req();
      send_rsp(req_q);
    join
  endtask : body


  virtual task get_req();
    forever begin
      spi_item req;
      p_sequencer.req_analysis_fifo.get(req);
      req_q.push_back(req);
    end
  endtask


  virtual task send_rsp(ref spi_item item_q[$]);
    forever begin
      wait(item_q.size > 0);
      rsp = item_q.pop_front();
      start_item(rsp);
      finish_item(rsp);
      get_response(rsp);
    end
  endtask


  virtual task get_nxt_req(ref spi_item item);
    wait  (req_q.size > 0);
    item = req_q.pop_front();
  endtask

endclass : spi_device_seq
