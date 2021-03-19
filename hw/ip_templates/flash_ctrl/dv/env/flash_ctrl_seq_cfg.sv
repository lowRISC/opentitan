// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class flash_ctrl_seq_cfg extends uvm_object;
  `uvm_object_utils(flash_ctrl_seq_cfg)

  // Randomization weights in percentages, and other related settings.

  // Maximun number of times the vseq is randomized and rerun.
  // TODO: This should move to `dv_base_seq_cfg`.
  uint max_num_trans;

  // Memory protection configuration.
  uint num_en_mp_regions;

  // This enables memory protection regions to overlap.
  bit allow_mp_region_overlap;

  // When this knob is NOT FlashOpInvalid (default) the selected operation will be the only operation to run in the test (FlashOpRead, FlashOpProgram, FlashOpErase).
  flash_ctrl_pkg::flash_op_e flash_only_op;

  // Weights to enable read / program and erase for each mem region.
  // TODO: Should these be per region?
  uint mp_region_read_en_pc;
  uint mp_region_program_en_pc;
  uint mp_region_erase_en_pc;
  uint mp_region_data_partition_pc;
  uint mp_region_max_pages;

  // Knob to control bank level erasability.
  uint bank_erase_en_pc;

  // Default region knobs.
  uint default_region_read_en_pc;
  uint default_region_program_en_pc;
  uint default_region_erase_en_pc;

  // Control the number of flash ops.
  uint max_flash_ops_per_cfg;

  // Flash ctrl op randomization knobs.
  
  // Partition select. Make sure to keep sum equals to 100.
  uint op_on_data_partition_pc;  // Choose data partition.
  uint op_on_info_partition_pc;  // Choose info partition.
  uint op_on_info1_partition_pc; // Choose info1 partition.
  uint op_on_red_partition_pc;   // Choose redundancy partition.

  bit op_readonly_on_info_partition;  // Make info partition read-only.
  bit op_readonly_on_info1_partition; // Make info1 partition read-only.


  uint op_erase_type_bank_pc;
  uint op_max_words;
  bit  op_allow_invalid;

  // Poll fifo status before writing to prog_fifo / reading from rd_fifo.
  uint poll_fifo_status_pc;

  `uvm_object_new

  // Set partition select percentages. Make sure to keep sum equals to 100.
  virtual function void set_partition_pc(uint sel_data_part_pc = 100,
                                         uint sel_info_part_pc = 0,
                                         uint sel_info1_part_pc = 0,
                                         uint sel_red_part_pc = 0);

    `DV_CHECK_EQ(sel_data_part_pc + sel_info_part_pc + sel_info1_part_pc + sel_red_part_pc, 100,
                        $sformatf("Error! sum of arguments must be 100. Be aware of arguments \
default values - 100 for data partition and 0 for all the others. Arguments current value: \
sel_data_part_pc=%0d , sel_info_part_pc=%0d , sel_info1_part_pc=%0d , sel_red_part_pc=%0d",
                                   sel_data_part_pc, sel_info_part_pc, sel_info1_part_pc,
                                   sel_red_part_pc))

    op_on_data_partition_pc = sel_data_part_pc;   // Percenteges to choose data partition.
    op_on_info_partition_pc = sel_info_part_pc;   // Percenteges to choose info partition.
    op_on_info1_partition_pc = sel_info1_part_pc; // Percenteges to choose info1 partition.
    op_on_red_partition_pc = sel_red_part_pc;     // Percenteges to choose redundancy partition.

  endfunction : set_partition_pc


  virtual function void configure();
    max_num_trans = 20;

    // Memory protection configuration.
    num_en_mp_regions = flash_ctrl_pkg::MpRegions;

    // This enables memory protection regions to overlap.
    allow_mp_region_overlap = 1'b0;

    // Weights to enable read / program and erase for each mem region.
    // TODO: Should these be per region?
    mp_region_read_en_pc = 50;
    mp_region_program_en_pc = 50;
    mp_region_erase_en_pc = 50;
    mp_region_data_partition_pc = 50;
    mp_region_max_pages = 32;

    // Knob to control bank level erasability.
    bank_erase_en_pc = 50;

    // Default region knobs.
    default_region_read_en_pc    = 50;
    default_region_program_en_pc = 50;
    default_region_erase_en_pc   = 50;

    // When this knob is not FlashOpInvalid the selected operation will be the only operation to run in the test (FlashOpRead, FlashOpProgram, FlashOpErase).
    flash_only_op = FlashOpInvalid;

    // Control the number of flash ops.
    max_flash_ops_per_cfg = 50;

    // Flash ctrl op randomization knobs.
    op_readonly_on_info_partition = 0; // Make info partition read-only.
    op_readonly_on_info1_partition = 0; // Make info1 partition read-only.

    op_erase_type_bank_pc = 0;
    op_max_words = 512;
    op_allow_invalid = 1'b0;

    // Poll fifo status before writing to prog_fifo / reading from rd_fifo.
    poll_fifo_status_pc = 30;

    set_partition_pc();

  endfunction : configure

endclass
