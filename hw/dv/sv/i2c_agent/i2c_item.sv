// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  // transaction data part
  bit [I2C_DATA_WIDTH-1:0] data_q[$];
  bit [I2C_ADDR_WIDTH-1:0] addr;
  int                      tran_id;
  int                      num_data;
  bus_op_e                 bus_op;
  drv_type_e               drv_type;
  // transaction control part
  bit                      nack;
  bit                      ack;
  bit                      rstart;
  bit [7:0]                fbyte;
  // random flags
  rand bit                 nakok, rcont, read, stop, start;

  constraint start_c     { start      inside {0, 1}; }
  constraint stop_c      { stop       inside {0, 1}; }
  constraint read_c      { read       inside {0, 1}; }
  constraint rcont_c     { rcont      inside {0, 1}; }
  constraint nakok_c     { nakok      inside {0, 1}; }

  `uvm_object_utils_begin(i2c_item)
    `uvm_field_int(tran_id,                 UVM_DEFAULT)
    `uvm_field_enum(bus_op_e,    bus_op,    UVM_DEFAULT)
    `uvm_field_int(addr,                    UVM_DEFAULT)
    `uvm_field_int(num_data,                UVM_DEFAULT)
    `uvm_field_queue_int(data_q,            UVM_DEFAULT)
    `uvm_field_int(start,                   UVM_DEFAULT)
    `uvm_field_int(stop,                    UVM_DEFAULT)
    //------
    `uvm_field_int(rstart,                  UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(ack,                     UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(nack,                    UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(read,                    UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(rcont,                   UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_int(nakok,                   UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
    `uvm_field_enum(drv_type_e,  drv_type,  UVM_DEFAULT | UVM_NOPRINT | UVM_NOCOMPARE)
  `uvm_object_utils_end

  `uvm_object_new

  function void clear_data();
    num_data = 0;
    addr     = 0;
    drv_type = None;
    data_q.delete();
  endfunction : clear_data

  function void clear_flag();
    start   = 1'b0;
    stop    = 1'b0;
    read    = 1'b0;
    rcont   = 1'b0;
    nakok   = 1'b0;
    rstart  = 1'b0;
  endfunction : clear_flag

  function void clear_all();
    clear_data();
    clear_flag();
  endfunction : clear_all

endclass : i2c_item
