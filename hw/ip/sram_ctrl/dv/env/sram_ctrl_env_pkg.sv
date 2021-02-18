// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sram_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import sram_ctrl_ral_pkg::*;
  import sram_ctrl_pkg::*;
  import otp_ctrl_pkg::*;
  import lc_ctrl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = { "fatal_parity_error" };
  parameter uint   NUM_ALERTS = 1;

  // Number of bits in the otp_ctrl_pkg::sram_otp_key_rsp_t struct:
  // 1 bit for valid, SramKeyWidth bits for the key, SramNonceWidth bits for the nonce.
  parameter int KDI_DATA_SIZE = 1 + otp_ctrl_pkg::SramKeyWidth + otp_ctrl_pkg::SramNonceWidth;

  // types
  typedef virtual mem_bkdr_if mem_bkdr_vif;
  typedef virtual sram_ctrl_lc_if lc_vif;

  // functions

  // package sources
  `include "sram_ctrl_env_cfg.sv"
  `include "sram_ctrl_env_cov.sv"
  `include "sram_ctrl_virtual_sequencer.sv"
  `include "sram_ctrl_scoreboard.sv"
  `include "sram_ctrl_env.sv"
  `include "sram_ctrl_vseq_list.sv"

endpackage
