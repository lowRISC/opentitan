// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A class wrapping a covergroup that tracks a single bit signal (and covers transitions with it
// toggling).
//
// Using a class like this allows the covergroup to be instantiated in multiple places (and in
// arrays).

class bit_toggle_cg_wrap;

  // A covergroup that tracks the value of some single-bit value (with associated coverpoint
  // cp_value). Tracking it explicitly with functional coverage allows transition bins (defined in
  // cp_transitions).
  //
  // If toggle_cov_en is true, the transitions in cp_transitions have nonzero weight.
  covergroup bit_toggle_cg(string name, bit toggle_cov_en = 1)
    with function sample(bit value);

    option.per_instance = 1;
    option.name         = name;

    cp_value: coverpoint value;
    cp_transitions: coverpoint value {
      option.weight = toggle_cov_en;
      bins rising  = (0 => 1);
      bins falling = (1 => 0);
    }
  endgroup : bit_toggle_cg

  function new(string name = "bit_toggle_cg_wrap", bit toggle_cov_en = 1);
    bit_toggle_cg = new(name, toggle_cov_en);
  endfunction : new

  // A wrapper around bit_toggle_cg.sample, allowing code using this class to call
  // the_class_instance.sample() in the same way as it would have sampled the underlying covergroup.
  function void sample(bit value);
    bit_toggle_cg.sample(value);
  endfunction : sample

endclass : bit_toggle_cg_wrap
