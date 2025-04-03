// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper class to hold tl_seq_item and a counter for scoreboarding purposes
class ac_range_check_scb_item extends uvm_object;
  `uvm_object_utils(ac_range_check_scb_item)

  tl_seq_item item;
  int         cnt;

  `uvm_object_new
endclass : ac_range_check_scb_item
