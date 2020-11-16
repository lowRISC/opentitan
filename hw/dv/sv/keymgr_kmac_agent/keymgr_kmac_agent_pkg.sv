// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_kmac_agent_pkg;
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

  `define CONNECT_DATA_WIDTH .HostDataWidth(keymgr_kmac_agent_pkg::KMAC_REQ_DATA_WIDTH)

  // package sources
  `include "keymgr_kmac_item.sv"
  `include "keymgr_kmac_agent_cfg.sv"
  `include "keymgr_kmac_sequencer.sv"
  `include "keymgr_kmac_agent_cov.sv"
  `include "keymgr_kmac_driver.sv"
  `include "keymgr_kmac_host_driver.sv"
  `include "keymgr_kmac_device_driver.sv"
  `include "keymgr_kmac_monitor.sv"
  `include "keymgr_kmac_seq_list.sv"
  `include "keymgr_kmac_agent.sv"

endpackage: keymgr_kmac_agent_pkg
