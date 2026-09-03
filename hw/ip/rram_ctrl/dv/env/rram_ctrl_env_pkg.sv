// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rram_ctrl_env_pkg;
  // Dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rram_ctrl_pkg::*;
  import rram_ctrl_core_ral_pkg::*;
  import rram_ctrl_host_ral_pkg::*;
  import rram_macro_prim_ral_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Parameters
  parameter uint   NUM_ALERTS = 5;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {
    "recov_err",
    "fatal_std_err",
    "fatal_err",
    "fatal_macro_err",
    "recov_macro_err"
  };

  // Frequency of the OTP interface clock (clk_otp_i). The testbench uses this to configure
  // otp_clk_rst_if directly.
  parameter uint OTP_CLK_FREQ_MHZ = 24;

  // Types
  typedef virtual rram_ctrl_otp_key_if otp_key_vif_t;

  typedef enum bit [1:0] {
    AddrRead  = 0,
    AddrWrite = 1,
    DataRead  = 2,
    DataWrite = 3
  } tl_phase_e;

  // Bit positions of the interrupts in intr_state/intr_enable/intr_test, matching
  // the order of the `interrupt_list` entries in data/rram_ctrl.hjson.
  typedef enum int {
    WrEmpty         = 0,
    WrLvl           = 1,
    RdFull          = 2,
    RdLvl           = 3,
    OpDone          = 4,
    CorrErr         = 5,
    NumRramCtrlIntr = 6
  } rram_ctrl_intr_e;

  // Write/read FIFO depths, mirroring rram_ctrl's WrFifoDepth/RdFifoDepth RTL
  // parameters. tb.sv uses these to parameterize the DUT instance directly.
  localparam int unsigned WrFifoDepth = 4;
  localparam int unsigned RdFifoDepth = 16;

  // Functions

  // Package sources
  `include "rram_ctrl_env_cfg.sv"
  `include "rram_ctrl_env_cov.sv"
  `include "rram_ctrl_virtual_sequencer.sv"
endpackage : rram_ctrl_env_pkg
