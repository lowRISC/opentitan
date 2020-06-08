// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package i2c_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local macros
  parameter uint I2C_ADDR_WIDTH = 7;
  parameter uint I2C_DATA_WIDTH = 8;

  typedef enum logic [3:0] {
    None, DevAck, RdData
  } drv_type_e;

  // register values
  typedef struct {
    // derived parameters
    bit [31:0]  tSetupStart;
    bit [31:0]  tHoldStart;
    bit [31:0]  tClockStart;
    bit [31:0]  tClockLow;
    bit [31:0]  tSetupBit;
    bit [31:0]  tClockPulse;
    bit [31:0]  tHoldBit;
    bit [31:0]  tClockStop;
    bit [31:0]  tSetupStop;
    bit [31:0]  tHoldStop;
    bit         enbTimeOut;
    bit [30:0]  tTimeOut;
  } timing_cfg_t;

  // forward declare classes to allow typedefs below
  typedef class i2c_item;
  typedef class i2c_agent_cfg;

  // package sources
  `include "i2c_item.sv"
  `include "i2c_agent_cfg.sv"
  `include "i2c_agent_cov.sv"
  `include "i2c_monitor.sv"
  `include "i2c_driver.sv"
  `include "i2c_device_driver.sv"
  `include "i2c_host_driver.sv"
  `include "i2c_sequencer.sv"
  `include "i2c_agent.sv"
  `include "seq_lib/i2c_seq_list.sv"

endpackage: i2c_agent_pkg
