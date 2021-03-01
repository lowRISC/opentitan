// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class flash_ctrl_seq_cfg extends uvm_object;
  `uvm_object_utils(flash_ctrl_seq_cfg)

  // Randomization weights in percentages, and other related settings.

  // Maximun number of times the vseq is randomized and rerun.
  // TODO: This should move to `dv_base_seq_cfg`.
  uint max_num_trans = 20;

  // Memory protection configuration.
  uint num_en_mp_regions = flash_ctrl_pkg::MpRegions;

  // This enables memory protection regions to overlap.
  bit allow_mp_region_overlap = 1'b0;

  // Weights to enable read / program and erase for each mem region.
  // TODO: Should these be per region?
  uint mp_region_read_en_pc = 50;
  uint mp_region_program_en_pc = 50;
  uint mp_region_erase_en_pc = 50;
  uint mp_region_data_partition_pc = 50;
  uint mp_region_max_pages = 32;

  // Knob to control bank level erasability.
  uint bank_erase_en_pc = 50;

  // Default region knobs.
  uint default_region_read_en_pc    = 50;
  uint default_region_program_en_pc = 50;
  uint default_region_erase_en_pc   = 50;

  // Control the number of flash ops.
  uint max_flash_ops_per_cfg = 50;

  // Flash ctrl op randomization knobs.
  
  // Partition select. Make sure to keep sum equals to 100.
  uint op_on_data_partition_pc = 100; // Choose data partition.
  uint op_on_info_partition_pc = 0;   // Choose info partition.
  uint op_on_info1_partition_pc = 0;  // Choose info1 partition.
  uint op_on_red_partition_pc = 0;    // Choose redundancy partition.

  uint op_erase_type_bank_pc = 0;
  uint op_max_words = 512;
  bit  op_allow_invalid = 1'b0;

  // Poll fifo status before writing to prog_fifo / reading from rd_fifo.
  uint poll_fifo_status_pc = 30;

  `uvm_object_new

endclass
