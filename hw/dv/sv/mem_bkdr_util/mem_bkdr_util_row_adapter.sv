// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Provide an abstract way to access the memory rows
//
// Integrators can subclass this to provide a specfic way of accessing a memory row
// and incorporate the phyical architecture.
//
class mem_bkdr_util_row_adapter;

  // A row might have additional extra bits
  protected uint32_t num_extra_bits = 0;

  // Return the number of extra bits of this row architecture
  function uint32_t get_num_extra_bits();
    return num_extra_bits;
  endfunction

  // Translates a raw encoded UVM data row from the memory in a contiguous
  // row of memory.
  //
  virtual function uvm_hdl_data_t decode_row(uvm_hdl_data_t read_data);
    return read_data;
  endfunction

  // Translates a contiguous UVM data row to the internal organization of a row
  // that can be written to the memory.
  //
  virtual function uvm_hdl_data_t encode_row(uvm_hdl_data_t write_data);
    return write_data;
  endfunction

  // Writes a 39 bit word into a decoded row data depending on the memory architecture

  // Given decoded `row_data`, a 39-bit `data` word to be written, and an address, return the
  // decoded row data with the data word at the correct position for the memory architecture and
  // the given address.
  virtual function uvm_hdl_data_t write_row_data_39b(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                     logic [38:0] data,
                                                     uvm_hdl_data_t row_data);
    row_data[38:0] = data;
    return row_data;
  endfunction

  // Reads a 39 bit word from decoded row data depending on the memory architecture

  // Given decoded `row_data` and an address, return the 39-bit data from the correct position
  // for the memory architecture and the given address.
  virtual function logic [38:0] read_row_data_39b(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                  uvm_hdl_data_t row_data);
    logic data;
    data = row_data[38:0];
    return data;
  endfunction

endclass
