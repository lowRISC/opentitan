// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// this object stores the cfg info for a command, so that when a driver/monitor receives a flash
// cmd, it knows how many addr_bytes, direction, dummy_cycles etc
class spi_flash_cmd_info extends uvm_sequence_item;
  rand bit [7:0] opcode;
  rand spi_flash_addr_mode_e addr_mode;
  rand bit write_command;
  // number of lanes when sending payload, set to 0 if no payload is expected
  rand bit [2:0] num_lanes;
  rand int dummy_cycles;
  // 2-stage read_pipeline enabled when >0
  rand bit [1:0] read_pipeline_mode;

  constraint addr_mode_c {
    // for dual/quad mode, it always contains address
    num_lanes > 1 -> addr_mode != SpiFlashAddrDisabled;
  }

  constraint num_lanes_c {
    write_command -> num_lanes == 1;
    num_lanes inside {0, 1, 2, 4};
  }

  constraint dummy_cycles_c {
    solve write_command before read_pipeline_mode;
    write_command  -> read_pipeline_mode == 0;
    !write_command -> read_pipeline_mode <= 2;

    // for dual/quad read, need at least 2 dummy cycles
    num_lanes > 1 && !write_command -> dummy_cycles >= 2;
    // write or no payload doesn't have dummy cycle.
    write_command || num_lanes == 0 -> dummy_cycles == 0;
    dummy_cycles dist {
      0     :/ 1,
      [1:7] :/ 1,
      8     :/ 1
    };
  }

  `uvm_object_utils_begin(spi_flash_cmd_info)
    `uvm_field_int(opcode,        UVM_DEFAULT)
    `uvm_field_enum(spi_flash_addr_mode_e, addr_mode, UVM_DEFAULT)
    `uvm_field_int(write_command, UVM_DEFAULT)
    `uvm_field_int(dummy_cycles,  UVM_DEFAULT)
    `uvm_field_int(num_lanes,     UVM_DEFAULT)
    `uvm_field_int(read_pipeline_mode, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
