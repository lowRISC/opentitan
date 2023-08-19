// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dma_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import mem_model_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import dma_ral_pkg::*;
  import dma_reg_pkg::*;
  import prim_mubi_pkg::*;
  import dma_pkg::*;
  import tlul_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  parameter uint NUM_MAX_OUTSTANDING_REQS = 2;   // Max Outstanding TL Requests

  // types
  typedef virtual dma_if dma_vif;
  //typedef virtual clk_if clk_rst_vif;
  typedef class dma_scoreboard;

  // DMAC Transfer width as encoded in
  // transfer_width register
  typedef enum {
    DmaXfer1BperTxn = 0,
    DmaXfer2BperTxn = 1,
    DmaXfer4BperTxn = 3
  } dma_transfer_width_e;

  // DMAC data direction in hardware handshake mode
  // enum values are based on dma hjson
  typedef enum {
    DmaRcvData = 0,
    DmaSendData = 1
  } dma_control_data_direction_e;

  // package sources
  `include "dma_seq_item.sv"
  `include "dma_handshake_mode_fifo.sv"
  `include "dma_env_cfg.sv"
  `include "dma_env_cov.sv"
  `include "dma_virtual_sequencer.sv"
  `include "dma_scoreboard.sv"
  `include "dma_env.sv"
  `include "dma_pull_seq.sv"
  `include "dma_vseq_list.sv"

endpackage
