// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_item extends uvm_sequence_item;

  // hold transaction type
  rand spi_trans_type_e item_type;
  // byte of data sent or received
  rand logic [7:0] data[$];
  // start of transaction
  bit first_byte;
  // flash command constraints
  rand int read_size;
  rand logic [7:0] payload_q[$];
  rand bit write_command;
  rand bit [7:0] address_q[$];
  rand bit [7:0] opcode;
  // 1,2 or 4 lanes for read response, 0 means no data
  rand bit [2:0] num_lanes;
  rand int dummy_cycles;
  rand int read_pipeline_mode;
  rand bit terminated_before_dummy_cycles;
  rand bit terminated_before_read_pipeline;

  // for dummy transaction
  rand uint dummy_sck_cnt;
  rand uint dummy_csb_length_ns;

  // indicate the active csb
  rand bit [CSB_WIDTH-1:0] csb_sel;

  // transaction status. only use in monitor on flash mode
  // allow scb to process payload when one byte data is received, instead
  // of wait until the entire item is collected. This indicates item has collected all data.
  bit mon_item_complete;

  // Triggered for each byte sampled and when CSB becomes inactive
  event byte_sampled_ev, dummy_cycles_ev, item_finished_ev;

  // constrain size of data sent / received to be at most 64kB
  constraint data_size_c { data.size() inside {[0:65536]}; }

  constraint dummy_sck_cnt_c {
    if (item_type == SpiTransSckNoCsb) {
      dummy_sck_cnt inside {[1:1000]};
    } else {
      dummy_sck_cnt == 0;
    }}

  constraint dummy_csb_length_ns_c {
    if (item_type == SpiTransCsbNoSck) {
      dummy_csb_length_ns inside {[1:1000]};
    } else {
      dummy_csb_length_ns == 0;
    }}

  constraint num_lanes_c {
    write_command -> num_lanes == 1;
    num_lanes inside {0, 1, 2, 4};
  }

  `uvm_object_utils_begin(spi_item)
    `uvm_field_enum(spi_trans_type_e, item_type, UVM_DEFAULT)
    `uvm_field_queue_int(data,                   UVM_DEFAULT)
    `uvm_field_int(first_byte,                   UVM_DEFAULT)
    `uvm_field_int(dummy_sck_cnt,                UVM_DEFAULT)
    `uvm_field_int(dummy_csb_length_ns,          UVM_DEFAULT)
    `uvm_field_int(read_size,                    UVM_DEFAULT)
    `uvm_field_int(write_command,                UVM_DEFAULT)
    `uvm_field_int(opcode,                       UVM_DEFAULT)
    `uvm_field_int(num_lanes,                    UVM_DEFAULT)
    `uvm_field_int(dummy_cycles,                 UVM_DEFAULT)
    `uvm_field_int(csb_sel,                      UVM_DEFAULT)
    `uvm_field_queue_int(payload_q,              UVM_DEFAULT)
    `uvm_field_queue_int(address_q,              UVM_DEFAULT)
    `uvm_field_int(read_pipeline_mode,           UVM_DEFAULT)
    `uvm_field_int(terminated_before_dummy_cycles,UVM_DEFAULT)
    `uvm_field_int(terminated_before_read_pipeline,UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void clear_all();
    data.delete();
  endfunction : clear_all

  function string convert2string();
    string txt="";

    txt = "\n \t ----| SPI ITEM |----";
    txt = {txt, $sformatf("\n ----| Item Type: \t%s", item_type.name()) };
    txt = {txt, $sformatf("\n ----| Dummy Clk Cnt: \t%0d",  dummy_sck_cnt) };
    txt = {txt, $sformatf("\n ----| Dummy Sck Lengtht: \t%0d ns",  dummy_csb_length_ns) };
    txt = {txt, $sformatf("\n ----| First Byte: \t%b ",  first_byte) };
    txt = {txt, $sformatf("\n ----| Data:") };

    foreach (data[i]) begin
      if (!i[2:0]) txt = {txt, "\n"};
      txt = {txt, $sformatf("%0h", data[i])};
    end
    return txt;
  endfunction // convert2string


endclass : spi_item
