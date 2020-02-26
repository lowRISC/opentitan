// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_item extends uvm_sequence_item;

  rand spi_trans_type_e item_type;
  // byte of data sent or received
  rand bit [7:0] data[$];

  rand uint dummy_clk_cnt;
  rand uint dummy_sck_length_ns;

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c {
    data.size() inside {[1:65536]};
  }

  constraint dummy_clk_cnt_c {
    dummy_clk_cnt inside {[1:1000]};
  }

  constraint dummy_sck_length_c {
    dummy_sck_length_ns inside {[1:1000]};
  }

  `uvm_object_utils_begin(spi_item)
    `uvm_field_enum(spi_trans_type_e, item_type, UVM_DEFAULT)
    `uvm_field_queue_int(data,              UVM_DEFAULT)
    `uvm_field_int(dummy_clk_cnt,           UVM_DEFAULT)
    `uvm_field_int(dummy_sck_length_ns,     UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
