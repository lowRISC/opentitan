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
  parameter uint MAX_CS = 4;
  parameter uint BYTE_ORDER = 1;  // must be same as ByteOrder defined in spi_host_reg_pkg

  // transaction type
  typedef enum {
    SpiTransNormal,    // normal SPI trans
    SpiTransSckNoCsb,  // bad SPI trans with clk but no sb
    SpiTransCsbNoScb   // bad SPI trans with csb but no clk
  } spi_trans_type_e;

  // sck edge type - used by driver and monitor
  // to wait for the right edge based on CPOL / CPHA
  typedef enum {
    LeadingEdge,
    DrivingEdge,
    SamplingEdge
  } sck_edge_type_e;

  // spi mode
  typedef enum logic [1:0] {
    Single  = 2'b00,  // Full duplex, tx: sio[0], rx: sio[1]
    Dual    = 2'b01,  // Half duplex, tx and rx: sio[1:0]
    Quad    = 2'b10,  // Half duplex, tx and rx: sio[3:0]
    Reserve = 2'b11
  } spi_mode_e;

  // spi direction
  typedef enum logic [1:0] {
    DummyCycles = 2'b00,
    RxOnly      = 2'b01,
    TxOnly      = 2'b10,
    RxTx        = 2'b11
  } spi_dir_e;

  // spi config
  typedef struct {
    // CONTROL register field
    rand bit [8:0]  tx_watermark;
    rand bit [6:0]  rx_watermark;
    rand bit        passthru;
    // CONFIGOPTS register field
    rand bit        cpol;
    rand bit        cpha;
    rand bit        fullcyc;
    rand bit [3:0]  csnlead;
    rand bit [3:0]  csntrail;
    rand bit [3:0]  csnidle;
    rand bit [15:0] clkdiv;
    // COMMAND register field
    rand spi_dir_e  direction;
    rand spi_mode_e speed;
    rand bit        csaat;
    rand bit [8:0]  len;
  } spi_regs_t;

  // forward declare classes to allow typedefs below
  typedef class spi_item;
  typedef class spi_agent_cfg;

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
