// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  // queue of data/addr
  bit [data_width-1:0] mem_datas[$];
  bit [addr_width-1:0] mem_addrs[$];
  // sampled signals to sb
  bit [data_width-1:0] rd_data;
  bit [data_width-1:0] wr_data;
  bit [addr_width-1:0] addr; // addr[0]=r/w bit

  rand int dly_to_send_nack;
  rand int dly_to_send_ack;
  rand int dly_to_send_stop;
  rand int dly_to_send_data;

  `uvm_object_utils_begin(i2c_item)
    `uvm_field_int(dly_to_send_nack, UVM_DEFAULT)
    `uvm_field_int(dly_to_send_ack,  UVM_DEFAULT)
    `uvm_field_int(dly_to_send_stop, UVM_DEFAULT)
    `uvm_field_int(dly_to_send_data, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_item
