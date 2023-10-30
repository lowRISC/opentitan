// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_dpe_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import keymgr_dpe_ral_pkg::*;
  import kmac_app_agent_pkg::*;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters and types
  parameter string LIST_OF_ALERTS[] = {"recov_operation_err", "fatal_fault_err"};
  parameter uint NUM_ALERTS = 2;
  parameter uint NUM_EDN = 1;
  parameter uint DIGEST_SHARE_WORD_NUM = keymgr_pkg::KeyWidth / TL_DW;

  typedef virtual keymgr_dpe_if keymgr_dpe_vif;
  typedef bit [keymgr_pkg::Shares-1:0][keymgr_pkg::KeyWidth-1:0] key_shares_t;
  typedef bit [keymgr_pkg::Shares-1:0][kmac_pkg::AppDigestW-1:0] kmac_digests_t;
  typedef enum {
    IntrOpDone,
    NumKeyMgrDpeIntr
  } keymgr_dpe_intr_e;

  typedef enum {
    Sealing,
    Attestation
  } keymgr_dpe_cdi_type_e;

  typedef enum {
    OtpRootKeyInvalid,
    OtpRootKeyValidLow,
    LcStateInvalid,
    OtpDevIdInvalid,
    RomDigestInvalid,
    RomDigestValidLow,
    FlashCreatorSeedInvalid,
    FlashOwnerSeedInvalid
  } keymgr_dpe_invalid_hw_input_type_e;

  typedef enum bit[1:0] {
    SideLoadNotAvail,
    SideLoadAvail,
    SideLoadClear
  } keymgr_dpe_sideload_status_e;

  typedef enum int {
    FaultOpNotOnehot,
    FaultOpNotConsistent,
    FaultOpNotExist,
    FaultKmacDoneError,
    FaultSideloadNotConsistent,
    FaultKeyIntgError
  } keymgr_dpe_fault_inject_type_e;

  string msg_id = "keymgr_dpe_env_pkg";
  // functions
  // state is incremental, if it's not in defined enum, consider as StDisabled
  function automatic keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e get_next_state(
      keymgr_dpe_pkg::keymgr_dpe_exposed_working_state_e current_state);

    uint next_state = int'(current_state) + 1;
    if (next_state >= int'(keymgr_dpe_pkg::StWorkDpeDisabled)) begin
      return keymgr_dpe_pkg::StWorkDpeDisabled;
    end else begin
      `downcast(get_next_state, next_state, , , msg_id);
    end
  endfunction

  // forward declaration
  typedef class keymgr_dpe_scoreboard;
  // package sources
  `include "keymgr_dpe_env_cfg.sv"
  `include "keymgr_dpe_env_cov.sv"
  `include "keymgr_dpe_virtual_sequencer.sv"
  `include "keymgr_dpe_scoreboard.sv"
  `include "keymgr_dpe_env.sv"
  `include "keymgr_dpe_vseq_list.sv"

endpackage
