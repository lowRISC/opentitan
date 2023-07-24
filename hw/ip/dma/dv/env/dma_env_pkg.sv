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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  parameter unit NUM_MAX_OUTSTANDING_REQS = 2;   // Max Outstanding TL Requests

  // types
  typedef virtual dma_if dma_vif;
  //typedef virtual clk_if clk_rst_vif;
  typedef class dma_scoreboard;

  // DMAC Address Space Register
  //    dma_address_space_id_source_asid
  //    dma_address_space_id_destination_asid
  //    0: OT Internal Private Space (eFuse, SRAM, ...: 32 bit addressing)
  //    1: SOC Control Register Address Space (CTN: 32 bit addressing)
  //    2: System Address Space (Host OS Managed SYS MEM and MMIO)
  //    3: OT External FLASH Address Space (QSPI)
  typedef enum bit [1:0] {
    DmaAddrSpaceOTInternalBUS,
    DmaAddrSpaceCTNReg32,
    DmaAddrSpaceSYS64,
    DmaAddrSpaceOTExternalFLASH
  } dma_address_space_id_t;

  // DMAC Transfer Size Register
  //    dma_transfer_size
  typedef enum bit [1:0] {
    DmaXfer1BperTxn,
    DmaXfer2BperTxn,
    DmaXfer3BperTxn,
    DmaXfer4BperTxn
  } dma_transfer_size_t;

  // DMAC Control Register
  //    dma_control_opcode
  typedef enum bit [3:0] {
    DmaOperCopy,
    DmaOperHash,
    DmaOperEncrypt,
    DmaOperDecrypt,
    DmaOperALU
  } dma_control_opcode_t;

  // DMAC Control Register
  //    dma_control_data_direction
  typedef enum bit {
    DmaRcvData,
    DmaSendData
  } dma_control_data_direction_t;

  // package sources
  `include "dma_env_cfg.sv"
  `include "dma_env_cov.sv"
  `include "dma_virtual_sequencer.sv"
  `include "dma_scoreboard.sv"
  `include "dma_env.sv"
  `include "dma_pull_seq.sv"
  `include "dma_seq_item.sv"
  `include "dma_vseq_list.sv"

endpackage
