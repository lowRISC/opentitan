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
  import prim_mubi_pkg::*;
  import dma_pkg::*;
  import tlul_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  parameter uint CTN_ADDR_WIDTH = 32;
  parameter uint CTN_DATA_WIDTH = 32;
  parameter uint HOST_ADDR_WIDTH = 32;
  parameter uint HOST_DATA_WIDTH = 32;
  parameter uint SYS_ADDR_WIDTH = 64;

  // Index of interrupt in intf_vif
  parameter uint DMA_DONE = 0;
  parameter uint DMA_ERROR = 1;
  parameter uint DMA_MEMORY_BUFFER_LIMIT_INTR = 2;

  // Completion status bits (DV-internal)
  typedef enum {
    StatusDone,
    StatusError,
    StatusAborted,
    StatusTimeout
  } status_e;
  // Bitmask of completion reason(s)
  typedef uint status_t;

  // types
  typedef virtual dma_if dma_vif;
  //typedef virtual clk_if clk_rst_vif;
  typedef class dma_scoreboard;

  // DMAC data direction in hardware handshake mode
  // enum values are based on dma hjson
  typedef enum {
    DmaRcvData = 0,
    DmaSendData = 1
  } dma_control_data_direction_e;

  typedef struct {
    asid_encoding_e src_id;
    asid_encoding_e dst_id;
  } addr_space_id_t;

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
