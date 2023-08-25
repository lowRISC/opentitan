// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// DMA Configuration Coverage
covergroup dma_config_cg with function sample(dma_seq_item item);
  option.per_instance = 1;
  option.name = "dma_config_cg";
  cp_src_asid: coverpoint item.src_asid;
  cp_dst_asid: coverpoint item.dst_asid;
  cp_data_size: coverpoint item.total_transfer_size {
    bins range[4] = {[0 : 3], // Smallest granularity which requires transfer_size=0
      [4 : 7], // Smallest default granularity
      [8 : 63], // Medium
      [64 : $] // Large
    };
  }
  cp_transfer_width: coverpoint item.per_transfer_width{
    bins one_byte = {0};
    bins two_byte = {1};
    bins fourbyte = {3};
  }
  cp_control_hwen: coverpoint item.handshake;
  cp_control_bufinc: coverpoint item.auto_inc_buffer;
  cp_control_fifoinc: coverpoint item.auto_inc_fifo;
  cp_control_dir: coverpoint item.direction;
  cp_range_unlock: coverpoint item.mem_range_unlock;
  cp_handshake_intr: coverpoint item.handshake_intr_en;
endgroup

// DMA Status Coverage
covergroup dma_status_cg with function sample(
  bit busy,
  bit done,
  bit aborted,
  bit error,
  bit[6:0] error_code,
  bit clear
);
  option.per_instance = 1;
  option.name = "dma_status_cg";
  cp_status_busy: coverpoint busy;
  cp_status_done: coverpoint done;
  cp_status_aborted: coverpoint aborted;
  cp_status_error: coverpoint error;
  cp_status_errcode: coverpoint error_code;
  cp_status_clear: coverpoint clear;
endgroup

class dma_env_cov extends cip_base_env_cov #(.CFG_T(dma_env_cfg));
  `uvm_component_utils(dma_env_cov)

  dma_config_cg config_cg;
  dma_status_cg status_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    config_cg = new();
    status_cg = new();
  endfunction: new

endclass
