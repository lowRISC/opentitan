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

  // local types
  // transaction type
  typedef enum {
    SpiTransNormal,    // normal SPI trans
    SpiTransSckNoCsb,  // bad SPI trans with clk but no sb
    SpiTransCsbNoScb   // bad SPI trans with csb but no clk
  } spi_trans_type_e;

  // sck edge type - used by driver and monitor to wait for the right edge based on CPOL / CPHA
  typedef enum {
    LeadingEdge,
    DrivingEdge,
    SamplingEdge
  } sck_edge_type_e;

  // spi mode
  typedef enum {
    Single = 0,  // Full duplex, tx: sio[0], rx: sio[1]
    Dual   = 1,  // Half duplex, tx and rx: sio[1:0]
    Quad   = 2   // Half duplex, tx and rx: sio[3:0]
  } spi_mode_e;

  // functions

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
  `include "spi_seq_list.sv"

endpackage: spi_agent_pkg
