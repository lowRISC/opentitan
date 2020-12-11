// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import keymgr_ral_pkg::*;
  import keymgr_kmac_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters and types
  parameter string LIST_OF_ALERTS[] = {"fault_err", "operation_err"};
  parameter uint NUM_ALERTS = 2;
  parameter keymgr_pkg::keymgr_ops_e ILLEGAL_OPS_B4_INIT[] = {
      keymgr_pkg::OpGenId,
      keymgr_pkg::OpGenSwOut,
      keymgr_pkg::OpGenHwOut,
      keymgr_pkg::OpDisable};
  parameter keymgr_pkg::keymgr_working_state_e LIST_OF_NORMAL_STATES[] = {
      keymgr_pkg::StInit,
      keymgr_pkg::StCreatorRootKey,
      keymgr_pkg::StOwnerIntKey,
      keymgr_pkg::StOwnerKey};

  typedef virtual keymgr_if keymgr_vif;
  typedef enum {
    IntrOpDone,
    NumKeyMgrIntr
  } keymgr_intr_e;

  // functions
  function automatic keymgr_pkg::keymgr_working_state_e get_next_state(
      keymgr_pkg::keymgr_working_state_e current_state);
    case (current_state)
      keymgr_pkg::StInit:           return keymgr_pkg::StCreatorRootKey;
      keymgr_pkg::StCreatorRootKey: return keymgr_pkg::StOwnerIntKey;
      keymgr_pkg::StOwnerIntKey:    return keymgr_pkg::StOwnerKey;
      keymgr_pkg::StOwnerKey:       return keymgr_pkg::StDisabled;
      default: return current_state;
    endcase
  endfunction

  // package sources
  `include "keymgr_env_cfg.sv"
  `include "keymgr_env_cov.sv"
  `include "keymgr_virtual_sequencer.sv"
  `include "keymgr_scoreboard.sv"
  `include "keymgr_env.sv"
  `include "keymgr_vseq_list.sv"

endpackage
