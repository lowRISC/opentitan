// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent_cfg extends dv_base_agent_cfg;
  // this parameters can be set by test to slow down the agent's responses
  int host_latency_cycles = 0;
  int device_latency_cycles = 0;

  i2c_target_addr_mode_e target_addr_mode = Addr7BitMode;

  timing_cfg_t    timing_cfg;
  bit host_stretch_test_mode = 0;

  virtual i2c_if  vif;

  bit     host_scl_start;
  bit     host_scl_stop;

  // In i2c test, between every transaction, assuming a new timing
  // parameter is programmed. This means during a transaction,
  // test should not update timing parameter.
  // This variable indicates target DUT receives the end of the transaction
  // and allow tb to program a new timing parameter.
  bit     got_stop = 0;

  int     sent_rd_byte = 0;
  int     rcvd_rd_byte = 0;

  // this variables can be configured from host test
  uint i2c_host_min_data_rw = 1;
  uint i2c_host_max_data_rw = 10;

  `uvm_object_utils_begin(i2c_agent_cfg)
    `uvm_field_int(en_monitor,                                UVM_DEFAULT)
    `uvm_field_enum(i2c_target_addr_mode_e, target_addr_mode, UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tSetupStart,                    UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tHoldStart,                     UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tClockStart,                    UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tClockLow,                      UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tSetupBit,                      UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tClockPulse,                    UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tHoldBit,                       UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tClockStop,                     UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tSetupStop,                     UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tHoldStop,                      UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tTimeOut,                       UVM_DEFAULT)
    `uvm_field_int(timing_cfg.enbTimeOut,                     UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tStretchHostClock,              UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tSdaUnstable,                   UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tSdaInterference,               UVM_DEFAULT)
    `uvm_field_int(timing_cfg.tSclInterference,               UVM_DEFAULT)

    `uvm_field_int(i2c_host_min_data_rw,                      UVM_DEFAULT)
    `uvm_field_int(i2c_host_max_data_rw,                      UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_agent_cfg
