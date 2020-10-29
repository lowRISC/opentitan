// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_model_item extends uvm_sequence_item;

  // What sort of transaction is this?
  otbn_model_item_type_e item_type;

  // Only valid when item_type == OtbnModelDone.
  bit                    err;

  `uvm_object_utils_begin(otbn_model_item)
    `uvm_field_enum (otbn_model_item_type_e, item_type, UVM_DEFAULT)
    `uvm_field_int  (err, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
