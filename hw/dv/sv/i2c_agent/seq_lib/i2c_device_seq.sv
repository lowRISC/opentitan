// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// --------------------
// Device sequence
// --------------------
class i2c_device_seq extends i2c_base_seq;

  `uvm_object_utils(i2c_device_seq)
  `uvm_object_new

  i2c_item req_q[$];

  virtual task body();
    fork
      forever begin
        i2c_item  req;
        p_sequencer.mon_item_fifo.get(req);
        req_q.push_back(req);
      end
      forever begin
        i2c_item  rsp;
        wait(req_q.size > 0);
        rsp = req_q.pop_front();
        start_item(rsp);
        finish_item(rsp);
      end
    join
  endtask
endclass : i2c_device_seq