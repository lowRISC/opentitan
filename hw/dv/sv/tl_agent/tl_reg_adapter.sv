// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class: register adapter type parameterized with the default tl_seq_item type. The idea is to
// extend tl_seq_item for further constraints or customizations if required and create the
// tl_reg_adapter instance with the overridden type.
class tl_reg_adapter #(type ITEM_T = tl_seq_item) extends uvm_reg_adapter;

  `uvm_object_param_utils(tl_reg_adapter#(ITEM_T))

  function new(string name = "tl_reg_adapter");
    super.new(name);
    supports_byte_enable = 1;
    provides_responses = 1;
  endfunction : new

  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    ITEM_T reg_item;
    reg_item = ITEM_T::type_id::create("reg_item");
    `DV_CHECK_RANDOMIZE_FATAL(reg_item)
    reg_item.a_addr   = rw.addr;
    reg_item.a_size   = 2; // 4 bytes
    reg_item.a_opcode = (rw.kind == UVM_WRITE) ? tlul_pkg::PutFullData : tlul_pkg::Get;
    reg_item.a_mask   = rw.byte_en;
    reg_item.a_data   = rw.data;
    `uvm_info(`gtn, $sformatf("tl reg req item: addr=0x%0h, op=%0s data=0x%0h",
                              reg_item.a_addr, reg_item.a_opcode.name, reg_item.a_data), UVM_HIGH)
    return reg_item;
  endfunction : reg2bus

  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    tl_seq_item reg_item;
    if (!$cast(reg_item, bus_item)) begin
      `uvm_fatal(`gtn, "Incorrect bus item type, expecting tl_seq_item");
    end
    rw.kind    = reg_item.a_opcode == tlul_pkg::PutFullData ? UVM_WRITE : UVM_READ;
    rw.addr    = reg_item.a_addr;
    rw.data    = (rw.kind == UVM_WRITE) ? reg_item.a_data : reg_item.d_data;
    rw.byte_en = reg_item.a_mask;
    rw.status  = reg_item.d_error? UVM_NOT_OK : UVM_IS_OK;
    `uvm_info(`gtn, $sformatf("tl reg rsp item: addr=0x%0h, op=%0s data=0x%0h",
                              rw.addr, rw.kind.name, rw.data), UVM_HIGH)
  endfunction: bus2reg

endclass : tl_reg_adapter

