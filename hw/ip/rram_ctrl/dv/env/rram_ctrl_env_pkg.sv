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
  import rram_ctrl_bkdr_util_pkg::*;
  import mem_bkdr_util_pkg::*;

  import prim_mubi_pkg::MuBi4True;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi4_t;
  import otp_ctrl_macro_pkg::cmd_e;
  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::On;
  import lc_ctrl_pkg::Off;

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

  // Types
  typedef virtual rram_ctrl_misc_io_if misc_vif_t;

  typedef enum bit [1:0] {
    AddrRead  = 0,
    AddrWrite = 1,
    DataRead  = 2,
    DataWrite = 3
  } tl_phase_e;

  typedef enum int {
    WrEmpty         = 0,
    WrLvl           = 1,
    RdFull          = 2,
    RdLvl           = 3,
    OpDone          = 4,
    CorrErr         = 5,
    NumRramCtrlIntr = 6
  } rram_ctrl_intr_e;

  localparam int unsigned WrFifoDepth = 4;
  localparam int unsigned RdFifoDepth = 16;

  // bus addr width
  typedef bit [BusAddrByteW-1:0] addr_t;
  // bus data words
  typedef logic [TL_DW-1:0] data_t;
  // queue of data words
  typedef data_t data_q_t[$];

  typedef struct packed {
    rram_part_e partition;   // data or info partition
    rram_op_e   op;          // read / write
    logic [9:0] num_words;   // number of words to read or write (TL_DW)
    addr_t      addr;        // starting addr for the op
  } rram_ctrl_op_t;

  // Functions

  // Package sources
  `include "rram_ctrl_env_cfg.sv"
  `include "rram_ctrl_env_cov.sv"
  `include "rram_ctrl_virtual_sequencer.sv"
  `include "rram_ctrl_scoreboard.sv"
  `include "rram_ctrl_env.sv"
  `include "rram_ctrl_vseq_list.sv"
endpackage : rram_ctrl_env_pkg
