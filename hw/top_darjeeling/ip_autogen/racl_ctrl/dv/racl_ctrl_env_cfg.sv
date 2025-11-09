// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An environment config for interfacing with racl_ctrl. This file expands from a template, allowing
// it to set ral_type_name to something that points at the templated register block. That is
// intended to be the only "templated bit": the guts of the logic for this class are in its ancestor
// classes.

class racl_ctrl_env_cfg extends racl_ctrl_base_env_pkg::racl_ctrl_base_env_cfg;
  `uvm_object_utils(racl_ctrl_env_cfg)
  extern function new (string name="");
endclass

function racl_ctrl_env_cfg::new (string name="");
  super.new(name);

  // Override ral_type_name so that the base class uses that, rather than its RAL_T parameter
  // (dv_base_reg_block).
  ral_type_name = racl_ctrl_reg_block::type_name;
endfunction
