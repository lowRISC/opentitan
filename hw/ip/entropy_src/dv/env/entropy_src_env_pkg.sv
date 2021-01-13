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
  import push_pull_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter bit [11:0][TL_DW-1:0] POR_ENTROPY = {32'h4836cb5a,
                                                 32'h7efd9124,
                                                 32'h836cb5a7,
                                                 32'hefd91248,
                                                 32'h36cb5a7e,
                                                 32'hfd912483,
                                                 32'h6cb5a7ef,
                                                 32'hd9124836,
                                                 32'hcb5a7efd,
                                                 32'h9124836c,
                                                 32'hb5a7efd9,
                                                 32'h124836cb};
  parameter string                LIST_OF_ALERTS[] = {"recov_alert_count_met"};
  parameter uint                  NUM_ALERTS = 1;

  // types
  typedef enum int {
    EntropyValid     = 0,
    HealthTestFailed = 1,
    FifoErr          = 2
  } entropy_src_intr_e;

  // package sources
  `include "entropy_src_env_cfg.sv"
  `include "entropy_src_env_cov.sv"
  `include "entropy_src_virtual_sequencer.sv"
  `include "entropy_src_scoreboard.sv"
  `include "entropy_src_env.sv"
  `include "entropy_src_vseq_list.sv"

endpackage
