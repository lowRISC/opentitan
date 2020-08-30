// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent_cfg extends dv_base_agent_cfg;

  bit en_monitor = 1'b1; // enable monitor
  i2c_target_addr_mode_e target_addr_mode = Addr7BitMode;

  timing_cfg_t    timing_cfg;

  virtual i2c_if  vif;

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
  `uvm_object_utils_end

  `uvm_object_new

endclass : i2c_agent_cfg
