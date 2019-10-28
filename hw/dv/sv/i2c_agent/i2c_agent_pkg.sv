// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef __I2C_AGENT_PKG__
`define __I2C_AGENT_PKG__

package i2c_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local macros
  `define I2C_DEVICE_DEFAULT_ADDR  7'h25
  `define I2C_DEVICE_MAX_ADDR      7'h7E
  `define I2C_DEVICE_ADDR_WIDTH    7        // only support 7 bit address mode
  `define I2C_FIFO_DATA_WIDTH      8
  `define I2C_FIFO_FLAG_WIDTH      5
  `define I2C_FMT_FIFO_WIDTH       (`I2C_FIFO_DATA_WIDTH + `I2C_FIFO_FLAG_WIDTH)
  `define I2C_RX_FIFO_WIDTH        (`I2C_FIFO_DATA_WIDTH)

  // local types
  typedef enum logic {
    WRITE  = 1'b0,
    READ   = 1'b1
  } i2c_rw_direction_e;

  typedef enum logic[2:0] {
    RESET      = 3'd0,
    FREE       = 3'd1,
    STOP       = 3'd2,
    START      = 3'd3,
    REPSTART   = 3'd4,
    ACK        = 3'd5,
    NACK       = 3'd6
  } i2c_bus_status_e;

  // forward declare classes to allow typedefs below
  typedef class i2c_item;
  typedef class i2c_agent_cfg;

  // reuse dv_base_seqeuencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T     (i2c_item),
                              .CFG_T      (i2c_agent_cfg)) i2c_sequencer;

  // package sources
  `include "i2c_item.sv"
  `include "i2c_agent_cfg.sv"
  `include "i2c_agent_cov.sv"
  `include "i2c_driver.sv"
  `include "i2c_host_driver.sv"
  `include "i2c_device_driver.sv"
  `include "i2c_monitor.sv"
  `include "i2c_agent.sv"
  `include "i2c_seq_list.sv"

endpackage: i2c_agent_pkg
`endif // __I2C_AGENT_PKG__
