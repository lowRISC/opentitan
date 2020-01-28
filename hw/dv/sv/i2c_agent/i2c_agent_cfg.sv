// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent_cfg extends dv_base_agent_cfg;

  // agent cfg knobs
  bit en_cov            = 1'b1; // enable coverage
  bit en_monitor        = 1'b1; // enable monitor
  if_mode_e             mode;   // host or device mode

  // random variable and their constrains
  int max_delay_ack  = 5;
  int max_delay_nack = 5;
  int max_delay_stop = 5;
  int max_delay_data = 5;

  // register values
  bit [31:0] status;           // status register
  bit [15:0] thigh;            // high period of the SCL in clock units
  bit [15:0] tlow;             // low period of the SCL in clock units
  bit [15:0] t_r;              // rise time of both SDA and SCL in clock units
  bit [15:0] t_f;              // fall time of both SDA and SCL in clock units
  bit [15:0] thd_sta;          // hold time for (repeated) START in clock units
  bit [15:0] tsu_sta;          // setup time for repeated START in clock units
  bit [15:0] tsu_sto;          // setup time for STOP in clock units
  bit [15:0] tsu_dat;          // data setup time in clock units
  bit [15:0] thd_dat;          // data hold time in clock units
  bit [15:0] t_buf;            // bus free time between STOP and START in clock units
  bit [30:0] timeout_val;      // max time target may stretch the clock
  bit        timeout_enb;      // assert if target stretches clock past max
  bit [15:0] tvd_ack = 1;      // minimum valid time for ack/nack (same to tvd_dat)
  
  // interface handle used by driver, monitor & the sequencer, via cfg handle
  virtual i2c_if  vif;

  `uvm_object_utils_begin(i2c_agent_cfg)
    `uvm_field_int(en_cov,           UVM_DEFAULT)
    `uvm_field_int(en_monitor,       UVM_DEFAULT)
    `uvm_field_enum(if_mode_e, mode, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_agent_cfg
