// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
class rjtag_seq_item extends uvm_sequence_item;

  rand bit [6:0]  dmi_addr  ; // DMI [6:0] address
  rand bit        dmi_wr    ; // Write or Read
  rand bit [31:0] dmi_wdata ; // Write data
       bit [31:0] dmi_rdata ; // Read data

  // Utility and Field macros,
  `uvm_object_utils_begin(rjtag_seq_item)
    `uvm_field_int  (dmi_addr, UVM_DEFAULT)
    `uvm_field_int  (dmi_wr,   UVM_DEFAULT)
    `uvm_field_int  (dmi_wdata,UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "rjtag_seq_item");
    super.new(name);
  endfunction : new

  // Constraints
  constraint addr_c {
    dmi_addr inside {'h10, 'h38, 'h39, 'h3C};
  }

endclass
