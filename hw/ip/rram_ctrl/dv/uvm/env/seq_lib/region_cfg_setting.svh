// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that represents the configuration that should be applied to a region through one of the
// MP_REGION_CFG_* registers.

class region_cfg_setting extends region_cfg_setting_base;
  `uvm_object_utils(region_cfg_setting)

  rand bit [3:0] m_en;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);

  // A soft constraint that requires the en field to be a valid mubi4_t value
  extern constraint vld_en_c;
endclass

function region_cfg_setting::new(string name="");
  super.new(name);
endfunction

function void region_cfg_setting::do_print(uvm_printer printer);
  super.do_print(printer);
  print_mubi4("m_en", m_en, printer);
endfunction

constraint region_cfg_setting::vld_en_c {
  soft m_en inside {MuBi4True, MuBi4False};
}
