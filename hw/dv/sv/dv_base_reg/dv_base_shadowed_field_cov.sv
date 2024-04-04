// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// coverage object of shadowed errors - update and storage errors.

class dv_base_shadowed_field_cov extends uvm_object;
  `uvm_object_utils(dv_base_shadowed_field_cov)

  covergroup shadow_field_errs_cg(string name) with function sample(bit update_err = 0,
                                                                    bit storage_err = 0);
    option.per_instance = 1;
    option.name         = name;

    cp_update_err: coverpoint update_err {
      bins update_err = {1};
    }

    cp_storage_err: coverpoint storage_err {
      bins storage_err = {1};
    }
  endgroup

  // use reg_field name as this name
  function new(string name = "");
    shadow_field_errs_cg = new($sformatf("%0s_shadowed_errs_cov", name));
  endfunction : new

endclass
