// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package alert_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_lib_pkg::*;
  import dv_utils_pkg::*;
  import prim_pkg::*;

  typedef class alert_seq_item;
  typedef class alert_agent_cfg;
  // reuse dv_base_driver as is with the right parameter set
  typedef dv_base_driver #(alert_seq_item, alert_agent_cfg) alert_base_driver;

  typedef enum {
    ping_trans,
    alert_trans,
    int_fail
  } alert_type_e;

  typedef enum {
    alert_received,
    ack_received,
    alert_complete,
    ack_complete
  } alert_handshake_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // include local files
  `include "alert_seq_item.sv"
  `include "alert_agent_cfg.sv"
  `include "alert_agent_cov.sv"
  `include "alert_sender_driver.sv"
  `include "alert_receiver_driver.sv"
  `include "alert_sequencer.sv"
  `include "alert_monitor.sv"
  `include "alert_agent.sv"
  `include "seq_lib/alert_receiver_alert_rsp_seq.sv"
  `include "seq_lib/alert_receiver_seq.sv"
  `include "seq_lib/alert_sender_ping_rsp_seq.sv"
  `include "seq_lib/alert_sender_seq.sv"
endpackage
