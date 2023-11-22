// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package mbx_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;
  import mbx_core_ral_pkg::*;
  import mbx_soc_ral_pkg::*;
  import mbx_mem_ral_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import mem_model_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter int unsigned NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault", "recov_fault"};

  parameter int unsigned MBX_DV_DW_SIZE_BYTES = 4;
  parameter int unsigned MBX_DV_MAX_DW = 1023;

  // types
  typedef int unsigned uint_t;
  typedef enum bit {
    READ = 0,
    WRITE = 1
  } reg_op_e;
  typedef enum {
    MbxCoreReady,
    MbxCoreAbort,
    MbxCoreError
  } mbx_core_intr_e;
  typedef enum {
    MbxSocDOE
  } mbx_soc_intr_e;

  // functions

  // package sources
  `include "mbx_env_cfg.sv"
  `include "mbx_env_cov.sv"
  `include "mbx_virtual_sequencer.sv"
  `include "mbx_scoreboard.sv"
  `include "mbx_env.sv"
  `include "mbx_vseq_list.sv"

endpackage: mbx_env_pkg
