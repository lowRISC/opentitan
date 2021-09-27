// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is the base proxy class for all the sec_cm interfaces.
class sec_cm_base_if_proxy extends uvm_object;
  sec_cm_type_e sec_cm_type;
  string prim_path;

  `uvm_object_new
  `uvm_object_utils_begin(sec_cm_base_if_proxy)
    `uvm_field_enum(sec_cm_type_e, sec_cm_type, UVM_DEFAULT)
  `uvm_object_utils_end


  virtual task inject_fault();
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask
  virtual task cleanup_fault();
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask
endclass
