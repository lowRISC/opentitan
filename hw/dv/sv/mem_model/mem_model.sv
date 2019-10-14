// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mem_model #(int AddrWidth = top_pkg::TL_AW,
                 int DataWidth = top_pkg::TL_DW) extends uvm_object;

  typedef bit [AddrWidth-1:0] mem_addr_t;
  typedef bit [DataWidth-1:0] mem_data_t;

  bit [7:0] system_memory[mem_addr_t];

  `uvm_object_param_utils(mem_model#(AddrWidth, DataWidth))

  function new(string name="");
    super.new(name);
  endfunction

  function bit [7:0] read_byte(mem_addr_t addr);
    bit [7:0] data;
    if (system_memory.exists(addr)) begin
      data = system_memory[addr];
      `uvm_info(get_full_name(),
                $sformatf("Read Mem  : Addr[0x%0h], Data[0x%0h]", addr, data), UVM_HIGH)
    end
    else begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `uvm_error(get_full_name(), $sformatf("read to uninitialzed addr 0x%0h", addr))
    end
    return data;
  endfunction

  function void write_byte(mem_addr_t addr, bit [7:0] data);
   `uvm_info(get_full_name(),
             $sformatf("Write Mem : Addr[0x%0h], Data[0x%0h]", addr, data), UVM_HIGH)
    system_memory[addr] = data;
  endfunction

  function void write(input mem_addr_t addr, mem_data_t data);
    bit [7:0] byte_data;
    for (int i = 0; i < DataWidth / 8; i++) begin
      byte_data = data[7:0];
      write_byte(addr + i, byte_data);
      data = data >> 8;
    end
  endfunction

  function mem_data_t read(mem_addr_t addr);
    mem_data_t data;
    for (int i = DataWidth / 8 - 1; i >= 0; i--) begin
      data = data << 8;
      data[7:0] = read_byte(addr + i);
    end
    return data;
  endfunction

endclass
