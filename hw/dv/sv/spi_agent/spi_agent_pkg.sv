// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package spi_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameter
  parameter uint MAX_CS = 4;      // set to the maximum valid value

  // transaction type
  typedef enum {
    // device dut
    SpiTransNormal,    // normal SPI trans
    SpiTransSckNoCsb,  // bad SPI trans with sck but no csb
    SpiTransCsbNoSck,   // bad SPI trans with csb but no sck
    SpiFlashTrans
  } spi_trans_type_e;

  // sck edge type - used by driver and monitor
  // to wait for the right edge based on CPOL / CPHA
  typedef enum {
    LeadingEdge,
    DrivingEdge,
    SamplingEdge
  } sck_edge_type_e;

  // spi mode
  typedef enum bit [1:0] {
    Standard = 2'b00,  // Full duplex, tx: sio[0], rx: sio[1]
    Dual     = 2'b01,  // Half duplex, tx and rx: sio[1:0]
    Quad     = 2'b10,  // Half duplex, tx and rx: sio[3:0]
    RsvdSpd  = 2'b11   // RFU
  } spi_mode_e;

  // spi functional mode
  typedef enum bit {
    FirmwareMode,
    FlashMode
  } spi_fw_flash_e;

  typedef enum bit [7:0] {
    ReadStd    = 8'b11001100,
    WriteStd   = 8'b11111100,
    ReadDual   = 8'b00000011,
    WriteDual  = 8'b00001100,
    ReadQuad   = 8'b00001111,
    WriteQuad  = 8'b11110000,
    CmdOnly    = 8'b10000001,
    ReadSts1   = 8'b00000101,
    ReadSts2   = 8'b00110101,
    ReadSts3   = 8'b00010101,
    ReadJedec  = 8'b10011111,
    ReadSfdp   = 8'b01011010
  } spi_cmd_e;

  // forward declare classes to allow typedefs below
  typedef class spi_item;
  typedef class spi_agent_cfg;

  class cmd_info extends uvm_sequence_item;
    rand byte op_code;
    rand bit [2:0] addr_bytes; // constrain to 0, 3 or 4
    rand bit write_command;
    rand bit [2:0] dummy_cycles; // TODO add support in driver and monitor
    rand bit [2:0] num_lanes;
    rand bit addr_swap;
    rand bit data_swap;

    constraint limitations_c {
      addr_bytes inside {0, 3, 4};
      num_lanes inside {1, 2, 4};
    }

    `uvm_object_utils_begin(cmd_info)
      `uvm_field_int(op_code,                   UVM_DEFAULT)
      `uvm_field_int(addr_bytes,                UVM_DEFAULT)
      `uvm_field_int(write_command,             UVM_DEFAULT)
      `uvm_field_int(dummy_cycles,              UVM_DEFAULT)
      `uvm_field_int(num_lanes,                 UVM_DEFAULT)
      `uvm_field_int(addr_swap,                 UVM_DEFAULT)
      `uvm_field_int(data_swap,                 UVM_DEFAULT)
    `uvm_object_utils_end

    `uvm_object_new
  endclass

  // package sources
  `include "spi_agent_cfg.sv"
  `include "spi_agent_cov.sv"
  `include "spi_item.sv"
  `include "spi_monitor.sv"
  `include "spi_driver.sv"
  `include "spi_host_driver.sv"
  `include "spi_device_driver.sv"
  `include "spi_sequencer.sv"
  `include "spi_agent.sv"
  `include "seq_lib/spi_seq_list.sv"

endpackage: spi_agent_pkg
