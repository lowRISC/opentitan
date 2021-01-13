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
  parameter uint DIGEST_SHARE_WORD_NUM = keymgr_pkg::KeyWidth / TL_DW;

  typedef virtual keymgr_if keymgr_vif;
  typedef bit [keymgr_pkg::Shares-1:0][keymgr_pkg::KeyWidth-1:0] key_shares_t;
  typedef enum {
    IntrOpDone,
    NumKeyMgrIntr
  } keymgr_intr_e;

  // functions
  // state is incremental, if it's not in defined enum, consider as StDisabled
  function automatic keymgr_pkg::keymgr_working_state_e get_next_state(
      keymgr_pkg::keymgr_working_state_e current_state);

    uint next_state = int'(current_state) + 1;
    if (next_state >= int'(keymgr_pkg::StDisabled)) begin
      return keymgr_pkg::StDisabled;
    end else begin
      return next_state;
    end


  endfunction

  // package sources
  `include "keymgr_env_cfg.sv"
  `include "keymgr_env_cov.sv"
  `include "keymgr_virtual_sequencer.sv"
  `include "keymgr_scoreboard.sv"
  `include "keymgr_env.sv"
  `include "keymgr_vseq_list.sv"

endpackage
