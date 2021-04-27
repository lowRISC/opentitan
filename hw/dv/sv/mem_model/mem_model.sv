// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mem_model #(int AddrWidth = bus_params_pkg::BUS_AW,
                  int DataWidth = bus_params_pkg::BUS_DW,
                  int MaskWidth = bus_params_pkg::BUS_DBW) extends uvm_object;

  typedef bit [AddrWidth-1:0] mem_addr_t;
  typedef bit [DataWidth-1:0] mem_data_t;
  typedef bit [MaskWidth-1:0] mem_mask_t;

  bit [7:0] system_memory[mem_addr_t];

  `uvm_object_param_utils(mem_model#(AddrWidth, DataWidth))

  `uvm_object_new

  function int get_written_bytes();
    return system_memory.size();
  endfunction

  function bit [7:0] read_byte(mem_addr_t addr);
    bit [7:0] data;
    if (system_memory.exists(addr)) begin
      data = system_memory[addr];
      `uvm_info(`gfn, $sformatf("Read Mem  : Addr[0x%0h], Data[0x%0h]", addr, data), UVM_HIGH)
    end else begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `uvm_error(`gfn, $sformatf("read to uninitialzed addr 0x%0h", addr))
    end
    return data;
  endfunction

  function void write_byte(mem_addr_t addr, bit [7:0] data);
   `uvm_info(`gfn, $sformatf("Write Mem : Addr[0x%0h], Data[0x%0h]", addr, data), UVM_HIGH)
    system_memory[addr] = data;
  endfunction

  function void compare_byte(mem_addr_t addr, bit [7:0] act_data);
   `uvm_info(`gfn, $sformatf("Compare Mem : Addr[0x%0h], Act Data[0x%0h], Exp Data[0x%0h]",
                             addr, act_data, system_memory[addr]), UVM_HIGH)
    system_memory[addr] = act_data;
    `DV_CHECK_EQ(act_data, system_memory[addr], $sformatf("addr 0x%0h read out mismatch", addr))
  endfunction

  function void write(input mem_addr_t addr, mem_data_t data, mem_mask_t mask = '1);
    bit [7:0] byte_data;
    for (int i = 0; i < DataWidth / 8; i++) begin
      if (mask[0]) begin
        byte_data = data[7:0];
        write_byte(addr + i, byte_data);
      end
      data = data >> 8;
      mask = mask >> 1;
    end
  endfunction

  function mem_data_t read(mem_addr_t addr, mem_mask_t mask = '1);
    mem_data_t data;
    for (int i = DataWidth / 8 - 1; i >= 0; i--) begin
      data = data << 8;
      if (mask[MaskWidth - 1]) data[7:0] = read_byte(addr + i);
      else                     data[7:0] = 0;
      mask = mask << 1;
    end
    return data;
  endfunction

  function void compare(mem_addr_t addr, mem_data_t act_data, mem_mask_t mask = '1);
    bit [7:0] byte_data;
    for (int i = 0; i < DataWidth / 8; i++) begin
      byte_data = act_data[7:0];
      if (mask[0]) begin
        compare_byte(addr + i, byte_data);
      end else begin
        // Nothing to do here: since this byte wasn't selected by the mask, there are no
        // requirements about what data came back.
      end
      act_data = act_data>> 8;
      mask = mask >> 1;
    end
  endfunction

endclass
