// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package entropy_src_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import entropy_src_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint ENTROPY_SRC_ADDR_MAP_SIZE = 64;
  parameter bit [3:0] POR_SEED = 4'hb;
  parameter bit [TL_DW-1:0] POR_ENTROPY = 32'h124836cb;

  // types
  typedef enum int {
    EntropyValid = 0,
    RctFailed = 1,
    AptFailed = 2,
    FifoErr = 3
  } entropy_src_intr_e;


  // functions

  // package sources
  `include "entropy_src_env_cfg.sv"
  `include "entropy_src_env_cov.sv"
  `include "entropy_src_virtual_sequencer.sv"
  `include "entropy_src_scoreboard.sv"
  `include "entropy_src_env.sv"
  `include "entropy_src_vseq_list.sv"

endpackage
