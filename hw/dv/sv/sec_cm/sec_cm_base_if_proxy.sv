// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is the base proxy class for all the sec_cm interfaces.
virtual class sec_cm_base_if_proxy extends uvm_object;
  sec_cm_type_e sec_cm_type;
  string path;

  `uvm_object_new

  pure virtual task automatic inject_fault();
  pure virtual task automatic restore_fault();
endclass
