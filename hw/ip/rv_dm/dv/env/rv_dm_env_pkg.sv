// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rv_dm_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import jtag_agent_pkg::*;
  import dv_lib_pkg::*;
  import rv_dm_params_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types

  // functions

  // package sources
  `include "rv_dm_reg_block.sv"
  `include "rv_dm_env_cfg.sv"
  `include "rv_dm_env_cov.sv"
  `include "rv_dm_virtual_sequencer.sv"
  `include "rv_dm_scoreboard.sv"
  `include "rv_dm_env.sv"
  `include "rv_dm_vseq_list.sv"

endpackage
