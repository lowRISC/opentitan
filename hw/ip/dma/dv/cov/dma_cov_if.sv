// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface dma_cov_if
  import dma_reg_pkg::*;
(
  input              clk,
  input dma_reg2hw_t reg2hw
);
  `include "dv_fcov_macros.svh"

  // DMA Configuration Coverage
  covergroup dma_config_cg @(posedge clk);
    cp_src_asid: coverpoint reg2hw.address_space_id.source_asid;
    cp_dst_asid: coverpoint reg2hw.address_space_id.destination_asid;
    cp_data_size: coverpoint reg2hw.total_data_size {
      bins range[4] = {
        [0:3], // Smallest granularity which requires transfer_width = 0
        [4:7], // Smallest default granularity
        [8:63], // Medium
        [64:$] // Large
      };
    }
    cp_transfer_width: coverpoint reg2hw.transfer_width {
      bins one_byte = {0};
      bins two_byte = {1};
      bins fourbyte = {3};
    }
    cp_control_hwen: coverpoint reg2hw.control.hardware_handshake_enable;
    cp_control_bufinc: coverpoint reg2hw.control.memory_buffer_auto_increment_enable;
    cp_control_fifoinc: coverpoint reg2hw.control.fifo_auto_increment_enable;
    cp_control_dir: coverpoint reg2hw.control.data_direction;
    cp_range_unlock: coverpoint reg2hw.range_unlock_regwen;
    cp_handshake_intr: coverpoint reg2hw.handshake_interrupt_enable;
  endgroup

  // DMA Status Coverage
  covergroup dma_status_cg @(posedge clk);
    cp_status_busy: coverpoint reg2hw.status.busy;
    cp_status_done: coverpoint reg2hw.status.done;
    cp_status_aborted: coverpoint reg2hw.status.aborted;
    cp_status_error: coverpoint reg2hw.status.error;
    cp_status_errcode: coverpoint reg2hw.status.error_code[5:0];
    cp_status_clear: coverpoint reg2hw.clear_state;
  endgroup

  // Interrupt-related Coverage
  covergroup dma_intr_state_cg @(posedge clk);
    cp_intr_done: coverpoint reg2hw.intr_state.dma_done;
    cp_intr_error: coverpoint reg2hw.intr_state.dma_error;
    cp_intr_membuf: coverpoint reg2hw.intr_state.dma_memory_buffer_limit;
  endgroup

  `DV_FCOV_INSTANTIATE_CG(dma_config_cg)
  `DV_FCOV_INSTANTIATE_CG(dma_status_cg)
  `DV_FCOV_INSTANTIATE_CG(dma_intr_state_cg)

endinterface
