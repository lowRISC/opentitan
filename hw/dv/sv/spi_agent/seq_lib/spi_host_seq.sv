// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_seq extends spi_base_seq;
  `uvm_object_utils(spi_host_seq)
  `uvm_object_new

  // data to be sent
  rand bit [7:0] data[$];

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c {
    data.size() inside {[1:65536]};
  }

  virtual task body();
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
  endtask

endclass
