// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A UVM sequence item that represents an error reported in an error log (the signal that a single
// RACL subscriber sends back to racl_ctrl).
//
// This is intended to wrap a value encoded in top_racl_pkg::racl_racl_error_log_t (when its valid
// flag is high)

class racl_error_log_item extends uvm_sequence_item;
  `uvm_object_utils(racl_error_log_item)

  // If this is true, it shows that the error log sender has seen more than one error log since last
  // being cleared (but is just reporting the first)
  rand bit          overflow;

  // The RACL role that was assigned to the actor trying to make the faulting access.
  rand int unsigned role;

  // The UID on the CTN of the actor trying to make the faulting access.
  rand int unsigned ctn_uid;

  // A flag that shows whether this was a read or write access.
  rand bit          read_not_write;

  // The address that the faulting access was trying to read/write.
  rand int unsigned request_address;

  extern function new (string name="");
  extern function void do_print(uvm_printer printer);
endclass

function racl_error_log_item::new(string name="");
  super.new(name);
endfunction

function void racl_error_log_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.print_int("overflow",        overflow,        1);
  printer.print_int("role",            role,            32);
  printer.print_int("ctn_uid",         ctn_uid,         32);
  printer.print_int("read_not_write",  read_not_write,  1);
  printer.print_int("request_address", request_address, 32);
endfunction
