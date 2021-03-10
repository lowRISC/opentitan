// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dcd_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import dcd_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types

  // functions

  // package sources
  `include "dcd_env_cfg.sv"
  `include "dcd_env_cov.sv"
  `include "dcd_virtual_sequencer.sv"
  `include "dcd_scoreboard.sv"
  `include "dcd_env.sv"
  `include "dcd_vseq_list.sv"

endpackage
