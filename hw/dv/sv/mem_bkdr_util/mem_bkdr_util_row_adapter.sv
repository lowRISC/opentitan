// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Provide an abstract way to access the memory rows
//
// Integrators can subclass this to privide a specfic way of accessing a memory row
// and incorporate the phyical architecture.
//
class mem_bkdr_util_row_adapter;

  // A row might have additional extra bits
  protected uint32_t num_extra_bits = 0;

  // Return the number of extra bits of this row architecture
  function uint32_t get_num_extra_bits();
    return num_extra_bits;
  endfunction

  // Translates a raw encoded UVM data row from the memory in a contigious
  // row of memory.
  //
  virtual function uvm_hdl_data_t decode_row(uvm_hdl_data_t read_data);
    return read_data;
  endfunction

  // Translates a contigious UVM data row to the internal organzation of a row
  // that can be written to the memory.
  //
  virtual function uvm_hdl_data_t encode_row(uvm_hdl_data_t write_data);
    return write_data;
  endfunction

  // Writes a 39 bit word into a decoded row data depending on the memory architecture
  virtual function uvm_hdl_data_t access_row_data39(bit [bus_params_pkg::BUS_AW-1:0] addr,
                                                    logic [38:0] data,
                                                    uvm_hdl_data_t row_data);
    row_data[38:0] = data;
    return row_data;
  endfunction
endclass
