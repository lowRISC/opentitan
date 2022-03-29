// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_item extends uvm_sequence_item;

  // hold transaction type
  rand spi_trans_type_e item_type;
  // byte of data sent or received
  rand bit [7:0] data[$];
  // start of transaction
  bit first_byte;
  // flash command constraints
  rand bit [7:0] read_bsize;
  rand bit [7:0] payload_q[$];
  rand bit write_command;
  rand bit [7:0] address_q[$];
  rand bit [7:0] opcode;
  rand bit [2:0] num_lanes; // 1,2 or 4 lanes for read response


  rand uint dummy_clk_cnt;
  rand uint dummy_sck_length_ns;

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c { data.size() inside {[1:65536]}; }

  constraint dummy_clk_cnt_c { dummy_clk_cnt inside {[1:1000]}; }

  constraint dummy_sck_length_c { dummy_sck_length_ns inside {[1:1000]}; }

  constraint num_lanes_c {
    write_command -> num_lanes == 1;
    num_lanes inside {1, 2, 4};
  }

  `uvm_object_utils_begin(spi_item)
    `uvm_field_enum(spi_trans_type_e, item_type, UVM_DEFAULT)
    `uvm_field_queue_int(data,                   UVM_DEFAULT)
    `uvm_field_int(first_byte,                   UVM_DEFAULT)
    `uvm_field_int(dummy_clk_cnt,                UVM_DEFAULT)
    `uvm_field_int(dummy_sck_length_ns,          UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void clear_all();
    data.delete();
  endfunction : clear_all

  function string convert2string();
    string txt="";

    txt = "\n \t ----| SPI ITEM |----";
    txt = {txt, $sformatf("\n ----| Item Type: \t%s", item_type.name()) };
    txt = {txt, $sformatf("\n ----| Dummy Clk Cnt: \t%0d",  dummy_clk_cnt) };
    txt = {txt, $sformatf("\n ----| Dummy Sck Lengtht: \t%0d ns",  dummy_sck_length_ns) };
    txt = {txt, $sformatf("\n ----| First Byte: \t%b ",  first_byte) };
    txt = {txt, $sformatf("\n ----| Data:") };

    foreach (data[i]) begin
      if (!i[2:0]) txt = {txt, "\n"};
      txt = {txt, $sformatf("%0h", data[i])};
    end
    return txt;
  endfunction // convert2string


endclass : spi_item
