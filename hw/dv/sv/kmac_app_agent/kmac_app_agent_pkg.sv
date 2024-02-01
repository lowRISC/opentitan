// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package kmac_app_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import keymgr_pkg::*;
  import push_pull_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter int KMAC_REQ_DATA_WIDTH = keymgr_pkg::KmacDataIfWidth       // data width
                                      + keymgr_pkg::KmacDataIfWidth / 8 // data mask width
                                      + 1;                              // bit last

  `define CONNECT_DATA_WIDTH .HostDataWidth(kmac_app_agent_pkg::KMAC_REQ_DATA_WIDTH)

  // package sources
  `include "kmac_app_item.sv"
  `include "kmac_app_agent_cfg.sv"
  `include "kmac_app_sequencer.sv"
  `include "kmac_app_agent_cov.sv"
  `include "kmac_app_driver.sv"
  `include "kmac_app_host_driver.sv"
  `include "kmac_app_device_driver.sv"
  `include "kmac_app_monitor.sv"
  `include "kmac_app_seq_list.sv"
  `include "kmac_app_agent.sv"

endpackage: kmac_app_agent_pkg
