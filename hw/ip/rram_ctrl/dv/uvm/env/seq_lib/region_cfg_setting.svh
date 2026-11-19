// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that represents the configuration that should be applied to a region through one of the
// MP_REGION_CFG_* registers.

class region_cfg_setting extends region_cfg_setting_base;
  rand bit [3:0] en;

  // An analogue of do_print that doesn't require this class to be a genuine uvm_object
  extern function void named_print(string name, uvm_printer printer);

  // A soft constraint that requires the en field to be a valid mubi4_t value
  extern constraint vld_en_c;
endclass

function void region_cfg_setting::named_print(string name, uvm_printer printer);
  // Note: This is not a virtual function: we print the base class fields directly here too.
  printer.print_generic(.name(name),
                        .type_name("region_cfg_setting"),
                        .size(20),
                        .value($sformatf({"{en: %0s, rd_en: %0s, wr_en: %0s, ",
                                          "scramble_en: %0s, ecc_en: %0s}"},
                                         format_mubi4(en), format_mubi4(rd_en), format_mubi4(wr_en),
                                         format_mubi4(scramble_en), format_mubi4(ecc_en))));
endfunction

constraint region_cfg_setting::vld_en_c {
  soft en inside {MuBi4True, MuBi4False};
}
