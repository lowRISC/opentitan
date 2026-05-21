// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package kmac_app_agent_pkg;
  // dep packages
  import uvm_pkg::*;

  import dv_utils_pkg::Host, dv_utils_pkg::Device;

  import dv_base_agent_pkg::dv_reactive_agent_cfg;
  import dv_base_agent_pkg::dv_base_agent_cov;
  import dv_base_agent_pkg::dv_base_driver;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_sequencer;
  import dv_base_agent_pkg::dv_base_agent;
  import dv_base_agent_pkg::dv_base_seq;

  import kmac_pkg::AppDigestW, kmac_pkg::MsgWidth;
  import kmac_pkg::rsp_digest_t;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  `include "kmac_app_req_item.sv"
  `include "kmac_app_req_packet_item.sv"
  `include "kmac_app_rsp_item.sv"
  `include "kmac_app_mon_item.sv"

  `include "kmac_app_agent_cfg.sv"
  typedef dv_base_agent_cov #(.CFG_T (kmac_app_agent_cfg)) kmac_app_agent_cov;
  `include "kmac_app_monitor.sv"

  `include "kmac_app_device_driver.sv"
  `include "kmac_app_device_sequencer.sv"

  `include "kmac_app_host_driver.sv"
  typedef dv_base_sequencer #(.ITEM_T (kmac_app_req_item),
                              .CFG_T (kmac_app_agent_cfg)) kmac_app_host_sequencer;

  `include "seq_lib/kmac_app_device_seq.sv"
  `include "seq_lib/kmac_app_host_seq.sv"

  `include "kmac_app_device_agent.sv"
  `include "kmac_app_host_agent.sv"

endpackage: kmac_app_agent_pkg
