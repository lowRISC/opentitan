// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is the (templated) environment package for a specialised instance of racl_ctrl. Most of the
// work normally done by an env_pkg is performed for racl_ctrl by racl_ctrl_base_env_pkg.

package racl_ctrl_env_pkg;
  import uvm_pkg::*;

  import racl_ctrl_ral_pkg::racl_ctrl_reg_block;

  // package sources
  `include "racl_ctrl_env_cfg.sv"
endpackage
