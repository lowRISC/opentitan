// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pattgen_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import pattgen_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import pattgen_reg_pkg::*;
  import pattgen_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  typedef enum int {
    DoneCh0        = 0,
    DoneCh1        = 1,
    NumPattgenIntr = 2
  } pattgen_intr_e;

  typedef enum bit[1:0] {
    NoChannels   = 2'b00,
    Channel0     = 2'b01,
    Channel1     = 2'b10,
    AllChannels  = 2'b11
  } channel_select_e;

  typedef enum bit {
    Enable      = 1'b1,
    Disable     = 1'b0
  } channel_status_e;

  // package sources
  `include "pattgen_seq_cfg.sv"
  `include "pattgen_channel_cfg.sv"
  `include "pattgen_env_cfg.sv"
  `include "pattgen_env_cov.sv"
  `include "pattgen_virtual_sequencer.sv"
  `include "pattgen_scoreboard.sv"
  `include "pattgen_env.sv"
  `include "pattgen_vseq_list.sv"

endpackage : pattgen_env_pkg
