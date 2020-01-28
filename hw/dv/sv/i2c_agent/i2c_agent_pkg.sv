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
  parameter uint addr_width = 8;     // [7:1]: device address, [0]: R/W bit
  parameter uint data_width = 8;

  typedef enum logic [3:0] {
    BusFree,
    HostSendStart, HostSendRestart, HostSendStop, HostSendAck, HostSendNoAck,
    HostSendAddr, HostSendRWBit, HostReceiveData, HostWriteData,
    TargetSendAck
  } bus_status_e;

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
  `include "i2c_sequencer.sv"
  `include "i2c_agent.sv"
  `include "i2c_seq_list.sv"

endpackage: i2c_agent_pkg
