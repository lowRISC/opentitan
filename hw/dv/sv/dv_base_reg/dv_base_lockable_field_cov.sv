// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// coverage object of lockable CSR field and its regwen
class dv_base_lockable_field_cov extends uvm_object;
  // mirrored value of the lockable field, which is used to know if new value is written.
  uvm_reg_data_t field_mirrored_val;
  // when new written value is different from mirrored value, this will be set.
  bit            is_new_val_written;
  // latched the regwen value when a new value is written to this lockable CSR.
  bit            regwen_val_when_new_value_written;

  `uvm_object_utils(dv_base_lockable_field_cov)

  // Cover these 2 cases
  // 1. When regwen = 1, write a non-mirrored value to lockable CSR and read it back
  // 2. When regwen = 0, write a non-mirrored value to lockable CSR and read it back
  covergroup regwen_val_when_new_value_written_cg(string name) with function sample();
    option.per_instance = 1;
    option.name         = name;

    cp_regwen: coverpoint regwen_val_when_new_value_written;
  endgroup : regwen_val_when_new_value_written_cg

  // use reg_field name as this name
  function new(string name = "");
    regwen_val_when_new_value_written_cg = new($sformatf("lockable_field_cov_of_%s", name));
  endfunction : new

  virtual function void reset(uvm_reg_data_t reset_val);
    field_mirrored_val = reset_val;
    is_new_val_written = 0;
  endfunction

  // invoke at dv_base_reg_field::post_write
  virtual function void post_write(uvm_reg_data_t new_val, bit regwen_val);
    if (field_mirrored_val != new_val) begin
      is_new_val_written                = 1;
      regwen_val_when_new_value_written = regwen_val;
      field_mirrored_val                = new_val;
    end
  endfunction

  // invoke at dv_base_reg_field::post_read
  virtual function void post_read();
    if (is_new_val_written) regwen_val_when_new_value_written_cg.sample();
  endfunction

endclass : dv_base_lockable_field_cov
