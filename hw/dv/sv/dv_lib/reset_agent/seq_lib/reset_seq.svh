// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_seq extends reset_base_seq;
  `uvm_object_utils(reset_seq)

  rand int unsigned assert_delay;
  rand int unsigned assert_width;

  // Constraints
  extern constraint assert_delay_c;
  extern constraint assert_width_c;

  // Standard SV/UVM methods
  extern function new (string name = "");
  extern task body();
endclass : reset_seq


constraint reset_seq::assert_delay_c {
  soft assert_delay inside {[10:1_000]};
}

constraint reset_seq::assert_width_c {
  soft assert_width inside {[10:1_000]};
}

function reset_seq::new(string name = "");
  super.new(name);
endfunction : new

task reset_seq::body();
  reset_item tr;
  tr = reset_item::type_id::create("tr");

  start_item(tr);

  if (!tr.randomize() with {
    assert_delay == local::assert_delay;
    assert_width == local::assert_width;
  }) `uvm_fatal(`gfn, "Failed to randomize transaction !")

  finish_item(tr);
endtask : body
