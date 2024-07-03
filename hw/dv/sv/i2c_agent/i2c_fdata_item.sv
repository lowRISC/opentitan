// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_fdata_item extends uvm_sequence_item;

  rand bit [7:0] fbyte;
  rand bit       start;
  rand bit       stop;
  rand bit       readb;
  rand bit       rcont;
  rand bit       nakok;

  `uvm_object_utils_begin(i2c_fdata_item)
    `uvm_field_int(fbyte,                      UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_int(start,                      UVM_DEFAULT)
    `uvm_field_int(stop,                       UVM_DEFAULT)
    `uvm_field_int(readb,                      UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_int(rcont,                      UVM_DEFAULT | UVM_NOCOMPARE)
    `uvm_field_int(nakok,                      UVM_DEFAULT | UVM_NOCOMPARE)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_fdata_item
