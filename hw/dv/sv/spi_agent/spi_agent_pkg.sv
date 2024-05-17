// Copyright lowRISC contributors (OpenTitan project).
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
  parameter uint TPM_START_MAX_WAIT_TIME_NS = 10_000_000; // 10ms
  parameter uint CSB_WIDTH = 2;
  parameter uint NUM_CSB = CSB_WIDTH ** 2;
  parameter time TIME_SCK_STABLE_TO_CSB_NS = 10ns;
  parameter uint TPM_ADDR_WIDTH      = 24;
  parameter uint TPM_ADDR_WIDTH_BYTE = TPM_ADDR_WIDTH / 8;
  parameter bit TPM_WAIT             = 1'b0;
  parameter bit TPM_START            = 1'b1;
  parameter byte MAX_TPM_SIZE        = 64;
  parameter byte TPM_CMD_DIR_BIT_POS = 7;
  parameter bit TPM_CMD_WRITE_BIT_VALUE = 0;
  parameter bit TPM_CMD_READ_BIT_VALUE  = 1;

  // transaction type
  typedef enum {
    // device dut
    SpiTransNormal,    // normal SPI trans
    SpiTransSckNoCsb,  // bad SPI trans with sck but no csb
    SpiTransCsbNoSck,  // bad SPI trans with csb but no sck
    SpiTransIncompleteOpcode  // bad SPI trans with incompleted opcode for flash/tpm mode only
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
  typedef enum bit [1:0] {
    SpiModeGeneric,
    SpiModeFlash,
    SpiModeTpm
  } spi_func_mode_e;

  // Command-Set implemented by the agent in device_mode.
  // The first byte in a transaction should be one of these commands.
  typedef enum bit [7:0] {
    ReadStd      = 8'b11001100,
    WriteStd     = 8'b11111100,
    ReadDual     = 8'b00000011,
    WriteDual    = 8'b00001100,
    ReadQuad     = 8'b00001111,
    WriteQuad    = 8'b11110000,
    CmdOnly      = 8'b10000001,
    AltCmd       = 8'b11111111 // Alternative command - used in spi_host to achieve
                               // alternative segment combinations
  } spi_cmd_e;

  typedef enum bit [1:0] {
    SpiFlashAddrDisabled,
    // Configurable 3b or 4b address
    SpiFlashAddrCfg,
    // Fixed 3b addr
    SpiFlashAddr3b,
    // Fixed 4b addr
    SpiFlashAddr4b
  } spi_flash_addr_mode_e;

  typedef enum bit [1:0] {
    SpiIdle,
    SpiCmd,
    SpiData
  } spi_fsm_e;

  // forward declare classes to allow typedefs below
  typedef class spi_item;
  typedef class spi_agent_cfg;

  string msg_id = "spi_agent_pkg";

  // formart: {write, 0, size-1 (6 bits)}
  function automatic bit [7:0] get_tpm_cmd(bit write, uint size);
    `DV_CHECK_LE(size, MAX_TPM_SIZE, , , msg_id)
    return {write ? TPM_CMD_WRITE_BIT_VALUE : TPM_CMD_READ_BIT_VALUE, 1'b0, 6'(size - 1)};
  endfunction

  function automatic void decode_tpm_cmd(input bit [7:0] cmd,
                                         output bit write, output uint size);
    write = (cmd[TPM_CMD_DIR_BIT_POS] == TPM_CMD_WRITE_BIT_VALUE) ? 1 : 0;
    `DV_CHECK_EQ(cmd[6], 0, , , msg_id)
    size = cmd[5:0] + 1;
    `DV_CHECK_LE(size, MAX_TPM_SIZE, , , msg_id)
  endfunction

  // package sources
  `include "spi_flash_cmd_info.sv"
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
