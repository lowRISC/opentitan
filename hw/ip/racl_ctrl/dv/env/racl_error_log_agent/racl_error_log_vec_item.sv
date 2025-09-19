// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A UVM sequence item that represents a state of a vector of error logs. It holds an associative
// array that gives items for each valid error.

class racl_error_log_vec_item extends uvm_sequence_item;
  `uvm_object_utils(racl_error_log_vec_item)

  // An associative array of items that give error signals in the vector. If subscriber i is
  // reporting an error, a racl_error_log_item representing that error will appear at index i in the
  // array.
  //
  // Although it's not marked "rand", this array *is* randomised, but the randomisation is done by
  // the post_randomize function.
  racl_error_log_item errors[int unsigned];

  // Subscribers with errors
  //
  // This is the set of indices for RACL subscribers that are reporting errors. It will be used in
  // the post_randomize function to randomize the errors array.
  rand int unsigned subscribers_with_errors[];

  extern function new (string name="");
  extern function void post_randomize();
  extern function void do_print(uvm_printer printer);
endclass

function racl_error_log_vec_item::new(string name="");
  super.new(name);
endfunction

function void racl_error_log_vec_item::post_randomize();
  foreach(subscribers_with_errors[i]) begin
    int unsigned sub_idx = subscribers_with_errors[i];
    errors[sub_idx] = racl_error_log_item::type_id::create($sformatf("errors[%d]", sub_idx));
    if (!errors[sub_idx].randomize()) begin
      `uvm_error(`gfn, $sformatf("Failed to randomize errors[%d]", sub_idx));
    end
  end
endfunction

function void racl_error_log_vec_item::do_print(uvm_printer printer);
  foreach (errors[i]) begin
    printer.print_object($sformatf("errors[%0d]", i), errors[i]);
  end
endfunction
