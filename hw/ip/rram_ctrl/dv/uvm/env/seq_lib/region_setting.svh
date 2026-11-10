// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class that represents the configuration that should be applied to a region through one of the
// MP_REGION_* registers.
//
// This is a class (rather than a struct) in order that it can be randomised

class region_setting;
  rand bit [11:0] base;
  rand bit [11:0] size;

  // An analogue of do_print that doesn't require this class to be a genuine uvm_object
  extern function void named_print(string name, uvm_printer printer);
endclass

function void region_setting::named_print(string name, uvm_printer printer);
  import rram_ctrl_reg_pkg::BytesPerPage;

  printer.print_generic(.name(name),
                        .type_name("region_setting"),
                        .size(24),
                        .value($sformatf("{base: 0x%0h, size: 0x%0h} (addresses 0x%0h..0x%0h)",
                                         base,
                                         size,
                                         base * BytesPerPage,
                                         ((base + size + 1) * BytesPerPage) - 1)));
endfunction
