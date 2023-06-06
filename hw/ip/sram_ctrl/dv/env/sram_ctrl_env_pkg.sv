// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sram_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import push_pull_agent_pkg::*;
  import sram_ctrl_regs_ral_pkg::*;
  import sram_ctrl_prim_ral_pkg::*;
  import sram_ctrl_pkg::*;
  import otp_ctrl_pkg::*;
  import lc_ctrl_pkg::*;
  import crypto_dpi_prince_pkg::*;
  import mem_bkdr_util_pkg::*;
  import mem_bkdr_scb_pkg::*;
  import prim_mubi_pkg::*;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = { "fatal_error"};
  parameter uint   NUM_ALERTS = 1;

  // Number of bits in the otp_ctrl_pkg::sram_otp_key_rsp_t struct:
  // 1 bit for valid, SramKeyWidth bits for the key, SramNonceWidth bits for the nonce.
  parameter int KDI_DATA_SIZE = 1 + otp_ctrl_pkg::SramKeyWidth + otp_ctrl_pkg::SramNonceWidth;

  // after a KDI transaction is completed, it needs 3 cycles in the SRAM clock domain
  // to be properly synchronized and propagated through the DUT
  parameter int KDI_PROPAGATION_CYCLES = 3;

  // a LC escalation request needs 3 cycles to be fully propagated through the DUT
  parameter int LC_ESCALATION_PROPAGATION_CYCLES = 3;

  // types
  typedef virtual sram_ctrl_lc_if lc_vif;
  typedef virtual sram_ctrl_exec_if exec_vif;

  typedef enum bit {
    SramCtrlRenewScrKey = 0,
    SramCtrlInit        = 1
  } sram_ctrl_e;

  typedef enum bit [2:0] {
    SramCtrlBusIntegError   = 0,
    SramCtrlInitError       = 1,
    SramCtrlEscalated       = 2,
    SramCtrlScrKeyValid     = 3,
    SramCtrlScrKeySeedValid = 4,
    SramCtrlInitDone        = 5
  } sram_ctrl_status_e;

  typedef class sram_ctrl_scoreboard;

  // package sources
  `include "sram_ctrl_env_cfg.sv"
  `include "sram_ctrl_env_cov.sv"
  `include "sram_ctrl_virtual_sequencer.sv"
  `include "sram_ctrl_mem_bkdr_scb.sv"
  `include "sram_ctrl_scoreboard.sv"
  `include "sram_ctrl_env.sv"
  `include "sram_ctrl_vseq_list.sv"

endpackage
