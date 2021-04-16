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

  // data to be sent
  rand bit [7:0] data[$];

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c {
    data.size() inside {[1:65536]};
  }

  virtual task body();
    // if mode = Dual/Quad then adopting re-active slave agent (half duplex)
    if (cfg.spi_mode != "Single") begin
      fork
        forever begin
          spi_item  req;
          p_sequencer.req_analysis_fifo.get(req);
          req_q.push_back(req);
        end
        forever begin
          spi_item  rsp;
          wait(req_q.size > 0);
          rsp = req_q.pop_front();
          start_item(rsp);
          finish_item(rsp);
        end
      join
    end else begin
    // if mode = Single then adopt full duplex
      req = spi_item::type_id::create("req");
      start_item(req);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                     item_type == SpiTransNormal;
                                     data.size() == local::data.size();
                                     foreach (data[i]) {
                                       data[i] == local::data[i];
                                     })
      finish_item(req);
      get_response(rsp);
    end
  endtask : body
  
endclass : spi_device_seq