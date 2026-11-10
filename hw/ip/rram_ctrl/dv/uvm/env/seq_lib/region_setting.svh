// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that represents the configuration that should be applied to a region through one of the
// MP_REGION_* registers.
//
// This is a class (rather than a struct) in order that it can be randomised

class region_setting extends uvm_object;
  `uvm_object_utils(region_setting)

  rand bit [11:0] m_base;
  rand bit [11:0] m_size;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);
endclass

function region_setting::new(string name="");
  super.new(name);
endfunction

function void region_setting::do_print(uvm_printer printer);
  import rram_ctrl_reg_pkg::BytesPerPage;

  super.do_print(printer);
  printer.print_field_int("m_base", m_base, 12, UVM_HEX);
  printer.print_field_int("m_size", m_size, 12, UVM_HEX);
  // Translating into a range of byte addresses (which is often what you actually want)
  printer.print_field_int("(min_addr)", m_base * BytesPerPage, 32, UVM_HEX);
  printer.print_field_int("(max_addr)", ((m_base + m_size + 1) * BytesPerPage) - 1, 32, UVM_HEX);
endfunction
