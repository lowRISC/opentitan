// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_device_seq extends i2c_base_seq;
  `uvm_object_utils(i2c_device_seq)
  `uvm_object_new

  rand bit [`I2C_DATA_WIDTH-1:0] rd_data;
  bit [`I2C_DATA_WIDTH-1:0] wr_data;
  bit [`I2C_ADDR_WIDTH-1:0] addr;
  bit [`I2C_DATA_WIDTH-1:0] mem_datas[$];
  bit [`I2C_ADDR_WIDTH-1:0] mem_addrs[$];

  task body();
    req = REQ::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        rd_data             == local::rd_data;
        mem_datas.size()    == local::mem_datas.size();
        mem_addrs.size()    == local::mem_addrs.size();
      )
    finish_item(req);
    get_response(rsp);
    `uvm_info(`gfn, "i2x device rsp done", UVM_HIGH)
  endtask

  virtual function void do_copy(uvm_object rhs);
    i2c_item rhs_;

    if (!$cast(rhs_, rhs)) begin
      `uvm_error({get_type_name(),":do_copy"}, "Copy Failed, type mismatch")
      return;
    end

    super.do_copy(rhs);
    addr             = rhs_.addr;
    rd_data          = rhs_.rd_data;
    wr_data          = rhs_.wr_data;
    foreach (rhs_.mem_datas[i]) mem_datas[i] = rhs_.mem_datas[i];
    foreach (rhs_.mem_addrs[i]) mem_addrs[i] = rhs_.mem_addrs[i];
  endfunction : do_copy

  function uvm_object clone();
    i2c_item t;
    t = new();
    t.do_copy(this);
    return t;
  endfunction : clone

endclass : i2c_device_seq
