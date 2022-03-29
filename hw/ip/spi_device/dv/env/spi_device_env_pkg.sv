// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package spi_device_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import spi_agent_pkg::*;
  import cip_base_pkg::*;
  import mem_model_pkg::*;
  import spi_device_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  typedef enum {
    RxFifoFull,
    RxFifoGeLevel,
    TxFifoLtLevel,
    RxFwModeErr,
    RxFifoOverflow,
    TxFifoUnderflow,
    CmdFifoNotEmpty,
    PayloadNotEmpty,
    PayloadOverflow,
    ReadbufWatermark,
    ReadbufFlip,
    TpmHeaderNotEmpty,
    NumSpiDevIntr
  } spi_device_intr_e;

  typedef enum bit {
    SramDataAvail,
    SramSpaceAvail
  } sram_avail_type_e;

  typedef enum bit {
    TpmFifoMode,
    TpmCrbMode
  } tpm_cfg_mode_e;

  typedef enum {
    GenericMode,
    FlashMode,
    PassthroughMode
  } device_mode_e;

  typedef enum {
    AddrDisabled,
    AddrCfg,
    Addr3B,
    Addr4B
  } addr_mode_e;

  typedef enum bit {
    PayloadIn,
    PayloadOut
  } payload_dir_e;

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // SPI SRAM is 2kB
  parameter uint SRAM_OFFSET                     = 'h1000;
  parameter uint SRAM_SIZE                       = 4096; // 672 depth
  parameter uint SRAM_MSB                        = $clog2(SRAM_SIZE) - 1;
  parameter uint SRAM_PTR_PHASE_BIT              = SRAM_MSB + 1;
  parameter uint SRAM_WORD_SIZE                  = 4;
  parameter uint ASYNC_FIFO_SIZE                 = 8;
  parameter bit[7:0] TPM_WRITE_CMD               = 8'hC0;
  parameter bit[7:0] TPM_READ_CMD                = 8'hC1;
  parameter byte TPM_START                       = 8'h01;
  parameter byte TPM_WAIT                        = 8'h00;
  parameter bit[11:0] TPM_HW_STS_OFFSET          = 12'h018;
  parameter bit[11:0] TPM_HW_INT_CAP_OFFSET      = 12'h014;
  parameter bit[23:0] TPM_BASE_ADDR              = 24'hD40000;
  parameter bit[7:0] READ_JEDEC                  = 8'h9F;
  parameter bit[7:0] READ_SFDP                   = 8'h5A;
  parameter bit[7:0] READ_STATUS_1               = 8'h05;
  parameter bit[7:0] READ_STATUS_2               = 8'h35;
  parameter bit[7:0] READ_STATUS_3               = 8'h15;
  parameter bit[7:0] READ_NORMAL                 = 8'h03;
  parameter bit[7:0] READ_FAST                   = 8'h0B;
  parameter bit[7:0] READ_DUAL                   = 8'h3B;
  parameter bit[7:0] READ_QUAD                   = 8'h6B;
  parameter bit[7:0] READ_DUALIO                 = 8'hBB;
  parameter bit[7:0] READ_QUADIO                 = 8'hEB;

  string msg_id = "spi_device_env_pkg";

  // functions
  // get size of empty space in mem
  function automatic uint get_sram_space_bytes(uint wptr, uint rptr, uint sram_size_bytes,
                                               string msg = msg_id);
    bit wptr_phase_bit = wptr[SRAM_PTR_PHASE_BIT];
    bit rptr_phase_bit = rptr[SRAM_PTR_PHASE_BIT];
    wptr[SRAM_PTR_PHASE_BIT] = 0;
    rptr[SRAM_PTR_PHASE_BIT] = 0;
    if (wptr_phase_bit == rptr_phase_bit) rptr += sram_size_bytes;
    `DV_CHECK_GE(rptr, wptr, "get_sram_space_bytes::", error, msg)
    return rptr - wptr;
  endfunction

  // get size of filled data in mem
  function automatic uint get_sram_filled_bytes(uint wptr, uint rptr, uint sram_size_bytes,
                                                string msg = msg_id);
    bit wptr_phase_bit = wptr[SRAM_PTR_PHASE_BIT];
    bit rptr_phase_bit = rptr[SRAM_PTR_PHASE_BIT];
    wptr[SRAM_PTR_PHASE_BIT] = 0;
    rptr[SRAM_PTR_PHASE_BIT] = 0;
    if (wptr_phase_bit != rptr_phase_bit) wptr += sram_size_bytes;
    `DV_CHECK_GE(wptr, rptr, "get_sram_filled_bytes", error, msg)
    return wptr - rptr;
  endfunction

  // get the memory size
  function automatic uint get_allocated_sram_size_bytes(uint base, uint limit);
    // Lower 2 bits are ignored
    base[1:0]  = 0;
    limit[1:0] = 0;
    return limit + SRAM_WORD_SIZE - base;
  endfunction

  // use this function to calculate the new ptr value
  // if new rx_rptr exceeds programmed sram size in bytes, then wrap it and flip the phase bit
  // else, restore the 'saved' phase bit
  function automatic uint get_sram_new_ptr(uint ptr,
                                           uint increment,
                                           uint sram_size_bytes);
    bit [TL_DW-1:0] ptr_wo_phase_bit = ptr[SRAM_MSB:0];
    bit             ptr_phase_bit    = ptr[SRAM_PTR_PHASE_BIT];
    uint            new_ptr          = ptr_wo_phase_bit + increment;
    if (new_ptr >= sram_size_bytes) begin
      new_ptr -= sram_size_bytes;
      new_ptr[SRAM_PTR_PHASE_BIT] = ~ptr_phase_bit;
    end else begin
      new_ptr[SRAM_PTR_PHASE_BIT] = ptr_phase_bit;
    end
    return new_ptr;
  endfunction

  // Get TPM address for locality TODO expand to other HW regs
  function automatic bit[23:0] get_tpm_addr(bit[3:0] locality);
    return TPM_BASE_ADDR | (locality << 12) | TPM_HW_STS_OFFSET;
  endfunction

  // macros
  `define GET_TX_ALLOCATED_SRAM_SIZE_BYTES \
    get_allocated_sram_size_bytes(ral.txf_addr.base.get_mirrored_value(), \
                                  ral.txf_addr.limit.get_mirrored_value())

  `define GET_RX_ALLOCATED_SRAM_SIZE_BYTES \
    get_allocated_sram_size_bytes(ral.rxf_addr.base.get_mirrored_value(), \
                                  ral.rxf_addr.limit.get_mirrored_value())

  // package sources
  `include "spi_device_env_cfg.sv"
  `include "spi_device_env_cov.sv"
  `include "spi_device_virtual_sequencer.sv"
  `include "spi_device_scoreboard.sv"
  `include "spi_device_env.sv"
  `include "spi_device_vseq_list.sv"

  `undef GET_TX_ALLOCATED_SRAM_SIZE_BYTES
  `undef GET_RX_ALLOCATED_SRAM_SIZE_BYTES
endpackage
