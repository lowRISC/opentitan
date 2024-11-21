// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_item extends uvm_sequence_item;
  rand int unsigned assert_delay;   // If reset is sync: number of clock cycles, async: time in ns
  rand int unsigned assert_width;   // If reset is sync: number of clock cycles, async: time in ns

  `uvm_object_utils_begin(reset_item)
    `uvm_field_int(assert_delay, UVM_DEFAULT)
    `uvm_field_int(assert_width, UVM_DEFAULT)
  `uvm_object_utils_end

  // Standard SV/UVM methods
  extern function new(string name = "");
  extern function string convert2string();
  extern function void do_print(uvm_printer printer);
  extern function void do_copy(uvm_object rhs);
  extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
endclass : reset_item


function reset_item::new(string name = "");
  super.new(name);
endfunction : new

function string reset_item::convert2string();
  string s = "";

  s = super.convert2string();
  s = {s, $sformatf("name         : %s\n", get_name())};
  s = {s, $sformatf("assert_delay : %0d\n", assert_delay)};
  s = {s, $sformatf("assert_width : %0d\n", assert_width)};
  return s;
endfunction : convert2string

function void reset_item::do_print(uvm_printer printer);
  super.do_print(printer);
  printer.m_string = $sformatf("%s\n", convert2string());
endfunction : do_print

function void reset_item::do_copy(uvm_object rhs);
  reset_item tr;

  // Attempt to convert the uvm_object into the actual transaction type: reset_item
  if (!$cast(tr, rhs)) begin
    uvm_report_error("do_copy:", "Cast failed");
    return;
  end

  super.do_copy(rhs); // Chain the copy with parent classes
  assert_delay  = tr.assert_delay;
  assert_width  = tr.assert_width;
endfunction : do_copy

function bit reset_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  reset_item tr;
  bit comp_status;

  if (!$cast(tr, rhs)) begin
    return 0;
  end

  comp_status = super.do_compare(rhs, comparer) &&
                (assert_delay == tr.assert_delay) &&
                (assert_width == tr.assert_width);

  return comp_status;
endfunction : do_compare
