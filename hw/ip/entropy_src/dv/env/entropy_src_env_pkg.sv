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
  parameter bit [TL_DW-1:0]   INCR_ENTROPY_LO  = 32'h76543210;
  parameter bit [TL_DW-1:0]   INCR_ENTROPY_HI  = 32'hfedcba98;
  parameter string            LIST_OF_ALERTS[] = {"recov_alert","fatal_alert"};
  parameter uint              NUM_ALERTS       = 2;

  // types
  typedef enum int {
    EntropyValid     = 0,
    HealthTestFailed = 1,
    EBusChkFailed    = 2,
    ObserveFifoReady = 3,
    FatalErr         = 4
  } entropy_src_intr_e;

  // package sources
  `include "entropy_src_env_cfg.sv"
  `include "entropy_src_env_cov.sv"
  `include "entropy_src_virtual_sequencer.sv"
  `include "entropy_src_scoreboard.sv"
  `include "entropy_src_env.sv"
  `include "entropy_src_vseq_list.sv"

endpackage
