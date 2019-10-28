// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent_cfg extends dv_base_agent_cfg;

  //*** agent cfg knobs
  bit is_active     = 1'b1; // active driver or passive monitor
  bit is_debug      = 1'b1; // use for debug
  bit en_cov        = 1'b1; // enable coverage
  bit en_rd_checks  = 1'b1; // enable RD checks (implemented in monitor)
  bit en_wr_checks  = 1'b1; // enable WR checks (implemented in monitor)
  bit en_rd_monitor = 1'b1; // enable RD monitor
  bit en_wr_monitor = 1'b1; // enable WR monitor

  //*** host mode cfg knobs
  bit en_host_drv   = 1'b0;     // enable host drive in agent

  //*** host drive cfg knobs
  bit en_device_drv = 1'b1;     // enable device drive in agent
  bit is_rw_device;
  // device target address to which the device will respond
  logic [`I2C_DEVICE_ADDR_WIDTH-1:0] device_addr;

  // device address and data fifos
  logic [`I2C_FMT_FIFO_WIDTH-1:0] device_fmt_fifo[$];
  logic [`I2C_RX_FIFO_WIDTH-1:0]  device_rx_fifo[$];

  // debug signal
  i2c_bus_status_e    i2c_bus_status;
  i2c_rw_direction_e  i2c_rw_direction;

  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual i2c_if vif;

  `uvm_object_utils_begin(i2c_agent_cfg)
    `uvm_field_int(is_active,    UVM_DEFAULT)
    `uvm_field_int(en_cov,       UVM_DEFAULT)
    `uvm_field_int(en_rd_checks, UVM_DEFAULT)
    `uvm_field_int(en_wr_checks, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_agent_cfg
