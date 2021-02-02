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
    NumSpiDevIntr
  } spi_device_intr_e;

  typedef enum bit {
    SramDataAvail,
    SramSpaceAvail
  } sram_avail_type_e;

  // SPI SRAM is 2kB
  parameter uint SRAM_OFFSET              = 'h1000;
  parameter uint SRAM_SIZE                = 4096; // 672 depth
  parameter uint SRAM_MSB                 = $clog2(SRAM_SIZE) - 1;
  parameter uint SRAM_PTR_PHASE_BIT       = SRAM_MSB + 1;
  parameter uint SRAM_WORD_SIZE           = 4;
  parameter uint ASYNC_FIFO_SIZE          = 8;

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
