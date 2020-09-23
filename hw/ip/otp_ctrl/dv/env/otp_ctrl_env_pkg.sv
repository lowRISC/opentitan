// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otp_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import otp_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // types
  typedef virtual pins_if #(3) pwr_otp_vif;
  typedef virtual mem_bkdr_if mem_bkdr_vif;

  typedef enum {
    OtpOperationDone,
    OtpErr
  } otp_intr_e;

  // functions

  // package sources
  `include "otp_ctrl_env_cfg.sv"
  `include "otp_ctrl_env_cov.sv"
  `include "otp_ctrl_virtual_sequencer.sv"
  `include "otp_ctrl_scoreboard.sv"
  `include "otp_ctrl_env.sv"
  `include "otp_ctrl_vseq_list.sv"

endpackage
