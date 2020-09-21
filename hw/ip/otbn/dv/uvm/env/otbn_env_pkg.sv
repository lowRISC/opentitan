// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otbn_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types
  typedef dv_base_reg_block otbn_reg_block;

  // functions

  // package sources
  `include "otbn_env_cfg.sv"
  `include "otbn_env_cov.sv"
  `include "otbn_virtual_sequencer.sv"
  `include "otbn_scoreboard.sv"
  `include "otbn_env.sv"
  `include "otbn_vseq_list.sv"

endpackage
