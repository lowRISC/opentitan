// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sysrst_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import sysrst_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};
  parameter uint   NUM_ALERTS = 1;

  parameter uint NumInputs = 7;

  typedef enum {
    IntrSysrstCtrl
  } sysrst_ctrl_intr_e;

  typedef enum {
    PwrbIdx = 0,
    Key0Idx = 1,
    Key1Idx = 2,
    Key2Idx = 3,
    AcPresentIdx = 4,
    EcRstIdx = 5,
    FlashWpIdx = 6,
    LidOpenIdx = 7
  } sysrst_input_idx_e;


  typedef struct {
    bit en_h2l;
    bit h2l_triggered;
  } edge_detect_h2l_t;

  typedef struct {
    bit en_l2h;
    bit l2h_triggered;
  } edge_detect_l2h_t;

  // package sources
  `include "sysrst_ctrl_env_cfg.sv"
  `include "sysrst_ctrl_env_cov.sv"
  `include "sysrst_ctrl_virtual_sequencer.sv"
  `include "sysrst_ctrl_scoreboard.sv"
  `include "sysrst_ctrl_env.sv"
  `include "sysrst_ctrl_vseq_list.sv"

endpackage
