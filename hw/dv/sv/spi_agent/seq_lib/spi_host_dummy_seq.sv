// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_dummy_seq extends spi_base_seq;
  `uvm_object_utils(spi_host_dummy_seq)
  `uvm_object_new

  virtual task body();
    req = spi_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   item_type inside {SpiTransSckNoCsb, SpiTransCsbNoScb};
                                   data.size() == 1; // no used, set to 1 to simpify randomization
                                   )
    finish_item(req);
    get_response(rsp);
  endtask

endclass
