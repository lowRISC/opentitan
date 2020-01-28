// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_item extends uvm_sequence_item;

  localparam MAX_DATA    = (1<<`I2C_DATA_WIDTH)-1;
  localparam MAX_ADDRESS = (1<<`I2C_ADDR_WIDTH)-1;

  // queue of data/addr tx/rx
  logic [`I2C_DATA_WIDTH-1:0] mem_datas[$];
  logic [`I2C_ADDR_WIDTH  :0] mem_addrs[$];

  // byte of data tx/rx
  rand logic [`I2C_DATA_WIDTH-1:0] rd_data;
  logic [`I2C_DATA_WIDTH-1:0] wr_data;
  logic [`I2C_ADDR_WIDTH-1:0] addr;      // addr[0]=R/W bit
  // number of bytes tx/rx
  int num_host_rd_byte;
  int num_host_wr_byte;

  // random constraints
  constraint mem_datas_c {
    mem_datas.size() inside {[1:65536]};
  }
  constraint mem_addrs_c {
    mem_addrs.size() inside {[1:65536]};
  }
  constraint rd_data_c {
    rd_data inside {[0:(1<<`I2C_DATA_WIDTH)-1]};
  }

  `uvm_object_utils_begin(i2c_item)
    `uvm_field_queue_int(mem_datas,  UVM_DEFAULT | UVM_NOPRINT)
    `uvm_field_queue_int(mem_addrs,  UVM_DEFAULT | UVM_NOPRINT)
    `uvm_field_int(rd_data,          UVM_DEFAULT)
    `uvm_field_int(wr_data,          UVM_DEFAULT)
    `uvm_field_int(addr,             UVM_DEFAULT)
    `uvm_field_int(num_host_rd_byte, UVM_DEFAULT)
    `uvm_field_int(num_host_wr_byte, UVM_DEFAULT)
  `uvm_object_utils_end

  function void do_copy(uvm_object rhs);
    i2c_item rhs_;

    if(!$cast(rhs_, rhs)) begin
      `uvm_fatal("do_copy", "cast of rhs object failed")
    end

    super.do_copy(rhs);
    // Copy over data members:
    mem_datas        = rhs_.mem_datas;
    mem_addrs        = rhs_.mem_addrs;
    wr_data          = rhs_.wr_data;
    rd_data          = rhs_.rd_data;
    addr             = rhs_.addr;
    num_host_rd_byte = rhs_.num_host_rd_byte;
    num_host_wr_byte = rhs_.num_host_wr_byte;
  endfunction : do_copy

  function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    i2c_item rhs_;

    if(!$cast(rhs_, rhs)) begin
      `uvm_error("do_copy", "cast of rhs object failed")
      return 0;
    end

    // delay is not relevant to the comparison
    return super.do_compare(rhs, comparer) &&
                  wr_data          == rhs_.wr_data &&
                  rd_data          == rhs_.rd_data &&
                  addr             == rhs_.addr    &&
                  num_host_rd_byte == rhs_.num_host_rd_byte &&
                  num_host_wr_byte == rhs_.num_host_wr_byte;
  endfunction : do_compare

  function void do_record(uvm_recorder recorder);
    super.do_record(recorder);

    // Use the record macros to record the item fields:
    `uvm_record_field("addr",             addr)
    `uvm_record_field("wr_data",          wr_data)
    `uvm_record_field("rd_data",          rd_data)
    `uvm_record_field("num_host_rd_byte", num_host_rd_byte)
    `uvm_record_field("num_host_wr_byte", num_host_wr_byte)
  endfunction:do_record

  `uvm_object_new

endclass : i2c_item
