// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_dummy_seq extends spi_base_seq;
  `uvm_object_utils(spi_host_dummy_seq)
  `uvm_object_new

  rand bit [CSB_WIDTH-1:0] csb_sel;
  rand bit [7:0] dummy_data;

  virtual task body();
    req = spi_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
                                   item_type inside {SpiTransSckNoCsb, SpiTransCsbNoSck,
                                                    SpiTransIncompleteOpcode};
                                   if (cfg.spi_func_mode == SpiModeGeneric) {
                                    item_type != SpiTransIncompleteOpcode;
                                   }
                                   csb_sel == local::csb_sel;
                                   data.size() == 1; // use for SpiTransIncompleteOpcode
                                   )
    finish_item(req);
    get_response(rsp);
  endtask

endclass
