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
  import sram_ctrl_regs_ral_pkg::*;
  import sram_ctrl_pkg::*;
  import otp_ctrl_pkg::*;
  import lc_ctrl_pkg::*;
  import crypto_dpi_prince_pkg::*;
  import mem_bkdr_util_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = { "fatal_intg_error", "fatal_parity_error"};
  parameter uint   NUM_ALERTS = 2;

  // Number of bits in the otp_ctrl_pkg::sram_otp_key_rsp_t struct:
  // 1 bit for valid, SramKeyWidth bits for the key, SramNonceWidth bits for the nonce.
  parameter int KDI_DATA_SIZE = 1 + otp_ctrl_pkg::SramKeyWidth + otp_ctrl_pkg::SramNonceWidth;

  // after a kDI transaction is copmleted, it needs 4 cycles in the SRAM clock domain
  // to be properly synchronized and propagated through the DUT
  parameter int KDI_PROPAGATION_CYCLES = 4;

  // a LC escalation request needs 3 cycles to be fully propagated through the DUT
  parameter int LC_ESCALATION_PROPAGATION_CYCLES = 3;

  // types
  typedef virtual sram_ctrl_lc_if lc_vif;
  typedef virtual sram_ctrl_exec_if exec_vif;

  typedef enum bit {
    SramCtrlRenewScrKey = 0,
    SramCtrlInit        = 1
  } sram_ctrl_e;

  typedef enum bit [1:0] {
    SramCtrlError           = 0,
    SramCtrlEscalated       = 1,
    SramCtrlScrKeyValid     = 2,
    SramCtrlScrKeySeedValid = 3
  } sram_ctrl_status_e;

  // package sources
  `include "sram_ctrl_env_cfg.sv"
  `include "sram_ctrl_env_cov.sv"
  `include "sram_ctrl_virtual_sequencer.sv"
  `include "sram_ctrl_scoreboard.sv"
  `include "sram_ctrl_env.sv"
  `include "sram_ctrl_vseq_list.sv"

endpackage
