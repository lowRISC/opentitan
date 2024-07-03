// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_acqdata_item extends uvm_sequence_item;

  rand bit [7:0] abyte;
  rand i2c_acq_byte_id_e signal;

  `uvm_object_utils_begin(i2c_acqdata_item)
    `uvm_field_int(abyte,                      UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_enum(i2c_acq_byte_id_e, signal, UVM_DEFAULT | UVM_NOCOMPARE)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_acqdata_item
