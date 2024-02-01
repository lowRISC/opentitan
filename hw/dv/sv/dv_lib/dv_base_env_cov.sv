// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class bit_toggle_cg_wrap;

  // Covergroup: bit_toggle_cg
  // Generic covergroup definition
  covergroup bit_toggle_cg(string name, string path = "", bit toggle_cov_en = 1) with function
        sample(bit value);
    option.per_instance = 1;
    option.name         = (path == "") ? name : {path, "::", name};

    cp_value: coverpoint value;
    cp_transitions: coverpoint value {
      option.weight = toggle_cov_en;
      bins rising  = (0 => 1);
      bins falling = (1 => 0);
    }
  endgroup : bit_toggle_cg

  // Function: new
  function new(string name = "bit_toggle_cg_wrap", string path = "", bit toggle_cov_en = 1);
    bit_toggle_cg = new(name, path, toggle_cov_en);
  endfunction : new

  // Function: sample
  function void sample(bit value);
    bit_toggle_cg.sample(value);
  endfunction : sample

endclass : bit_toggle_cg_wrap

class dv_base_env_cov #(type CFG_T = dv_base_env_cfg) extends uvm_component;
  `uvm_component_param_utils(dv_base_env_cov #(CFG_T))

  CFG_T cfg;

  `uvm_component_new

endclass
