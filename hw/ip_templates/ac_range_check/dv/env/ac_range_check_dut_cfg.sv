// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This class is a bundle that contains all the configuration parameters for the DUT. This avoids
// repeating the variable declaration multiple times. On the other hand, their constraints must not
// be contained in this file, but directly in the files where they are needed as this may lead to
// some conflicts.
class ac_range_check_dut_cfg extends uvm_object;
  rand bit [TL_DW-1:0] range_base[NUM_RANGES];  // Granularity is 32-bit words, 2-LSBs are ignored
  rand bit [TL_DW-1:0] range_limit[NUM_RANGES]; // Granularity is 32-bit words, 2-LSBs are ignored
  rand range_attr_t    range_attr[NUM_RANGES];
  rand racl_policy_t   range_racl_policy[NUM_RANGES];

  // Standard SV/UVM methods
  extern function new(string name="");
  extern function void post_randomize();
  extern function void do_print(uvm_printer printer);

  // UVM Factory Registration Macro
  `uvm_object_utils_begin (ac_range_check_dut_cfg)
    `uvm_field_sarray_int(range_base, UVM_DEFAULT)
    `uvm_field_sarray_int(range_limit, UVM_DEFAULT)
  `uvm_object_utils_end
endclass : ac_range_check_dut_cfg


function ac_range_check_dut_cfg::new(string name="");
  super.new(name);
endfunction : new

function void ac_range_check_dut_cfg::post_randomize();
  if (uvm_top.get_report_verbosity_level() >= UVM_HIGH) begin
    this.print();
  end
endfunction : post_randomize

// Some types are unsupported by the macros and have to be implemented manually
function void ac_range_check_dut_cfg::do_print(uvm_printer printer);
  `uvm_info(this.get_name(), "do_print function has been called", UVM_DEBUG);
  super.do_print(printer);

  foreach (range_attr[i]) begin
    printer.print_field($sformatf("range_attr[%0d]", i), "range_attr_t", $bits(range_attr[i]),
                        $sformatf("%p", range_attr[i]));
  end

  foreach (range_racl_policy[i]) begin
    printer.print_field($sformatf("range_racl_policy[%0d]", i), "racl_policy_t",
                        $bits(range_racl_policy[i]), $sformatf("%p", range_racl_policy[i]));
  end
endfunction: do_print
