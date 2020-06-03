// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pattgen_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import pattgen_reg_pkg::*;
  import pattgen_ral_pkg::*;

  // macro includes
  `include "dv_macros.svh"

  // parameters
  typedef enum int {
    PattDone0      = 0,
    PattDone1      = 1,
    NumI2cIntr     = 2
  } pattgen_intr_e;

  // csr and mem total size for IP, TODO confirm below value with spec
  parameter uint PATTGEN_ADDR_MAP_SIZE = 128;

  // package sources
  `include "pattgen_env_cfg.sv"
  `include "pattgen_env_cov.sv"
  `include "pattgen_virtual_sequencer.sv"
  `include "pattgen_scoreboard.sv"
  `include "pattgen_env.sv"
  `include "pattgen_vseq_list.sv"

endpackage : pattgen_env_pkg
