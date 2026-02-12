// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A small extension of racl_error_log_vec_item that adds a delay field, for use with a driver. This
// allows a sequence to send back-to-back items but not change value every cycle.

class racl_error_log_vec_driver_item extends racl_error_log_vec_item;
  `uvm_object_utils(racl_error_log_vec_driver_item)

  // The number of cycles to wait before driving the underlying item.
  rand int unsigned delay;

  extern function new (string name="");
endclass

function racl_error_log_vec_driver_item::new(string name="");
  super.new(name);
endfunction
