// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package usb20_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint FS_PERIOD_PS = 83333;

  // local types
  // forward declare classes to allow typedefs below
  typedef class usb20_item;
  typedef class usb20_agent_cfg;

  // add typedef for usb20_driver which is dv_base_driver with the right parameter set
  // usb20_host_driver and usb20_device_driver will extend from this
  typedef dv_base_driver #(.ITEM_T        (usb20_item),
                           .CFG_T         (usb20_agent_cfg)) usb20_driver;

  // reuse dv_base_seqeuencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T     (usb20_item),
                              .CFG_T      (usb20_agent_cfg)) usb20_sequencer;

  // functions

  // package sources
  `include "usb20_item.sv"
  `include "usb20_agent_cfg.sv"
  `include "usb20_agent_cov.sv"
  `include "usb20_host_driver.sv"
  `include "usb20_device_driver.sv"
  `include "usb20_monitor.sv"
  `include "usb20_agent.sv"
  `include "usb20_seq_list.sv"

endpackage: usb20_agent_pkg
