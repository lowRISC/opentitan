// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that represents the configuration that should be applied to the default region through
// DEFAULT_REGION.
//
// It acts as a base class for region_cfg_setting (used for the MP_REGION_CFG_* registers).

class region_cfg_setting_base extends uvm_object;
  `uvm_object_utils(region_cfg_setting_base)

  rand bit [3:0] m_rd_en;
  rand bit [3:0] m_wr_en;
  rand bit [3:0] m_scramble_en;
  rand bit [3:0] m_ecc_en;

  extern function new(string name="");
  extern virtual function void do_print(uvm_printer printer);

  // Print a mubi4_t to printer with enum name and binary value
  extern protected function void print_mubi4(string name, bit [3:0] value, uvm_printer printer);

  // Soft constraints that require all of the fields in the class to be valid mubi4_t values
  extern constraint vld_mubi_c;
endclass

function region_cfg_setting_base::new(string name="");
  super.new(name);
endfunction

function void region_cfg_setting_base::do_print(uvm_printer printer);
  super.do_print(printer);
  print_mubi4("m_rd_en", m_rd_en, printer);
  print_mubi4("m_wr_en", m_wr_en, printer);
  print_mubi4("m_scramble_en", m_scramble_en, printer);
  print_mubi4("m_ecc_en", m_ecc_en, printer);
endfunction

function void region_cfg_setting_base::print_mubi4(string      name,
                                                   bit [3:0]   value,
                                                   uvm_printer printer);
  mubi4_t upcast = mubi4_t'(value);
  string  upcast_name = upcast.name();
  printer.print_generic(name, "mubi4_t", 4,
                        $sformatf("%0s (0x%0h)",
                                  (upcast_name == "" ? "??" : upcast_name), value));
endfunction

constraint region_cfg_setting_base::vld_mubi_c {
  soft m_rd_en inside {MuBi4True, MuBi4False};
  soft m_wr_en inside {MuBi4True, MuBi4False};
  soft m_scramble_en inside {MuBi4True, MuBi4False};
  soft m_ecc_en inside {MuBi4True, MuBi4False};
}
