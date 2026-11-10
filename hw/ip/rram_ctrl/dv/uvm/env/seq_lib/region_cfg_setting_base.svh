// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that represents the configuration that should be applied to the default region through
// DEFAULT_REGION.
//
// It acts as a base class for region_cfg_setting (used for the MP_REGION_CFG_* registers).

class region_cfg_setting_base;
  rand bit [3:0] rd_en;
  rand bit [3:0] wr_en;
  rand bit [3:0] scramble_en;
  rand bit [3:0] ecc_en;

  // An analogue of do_print that doesn't require this class to be a genuine uvm_object
  extern function void named_print(string name, uvm_printer printer);
  extern protected function string format_mubi4(bit [3:0] value);

  // Soft constraints that require all of the fields in the class to be valid mubi4_t values
  extern constraint vld_mubi_c;
endclass

function void region_cfg_setting_base::named_print(string name, uvm_printer printer);
  printer.print_generic(.name(name),
                        .type_name("region_cfg_setting_base"),
                        .size(16),
                        .value($sformatf({"{rd_en: %0s, wr_en: %0s, ",
                                          "scramble_en: %0s, ecc_en: %0s}"},
                                         format_mubi4(rd_en), format_mubi4(wr_en),
                                         format_mubi4(scramble_en), format_mubi4(ecc_en))));
endfunction

function string region_cfg_setting_base::format_mubi4(bit [3:0] value);
  mubi4_t upcast = mubi4_t'(value);
  string  upcast_name = upcast.name();

  return $sformatf("%0s (0x%0h)", (upcast_name == "" ? "??" : upcast_name), value);
endfunction

constraint region_cfg_setting_base::vld_mubi_c {
  soft rd_en inside {MuBi4True, MuBi4False};
  soft wr_en inside {MuBi4True, MuBi4False};
  soft scramble_en inside {MuBi4True, MuBi4False};
  soft ecc_en inside {MuBi4True, MuBi4False};
}
