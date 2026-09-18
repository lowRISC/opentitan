// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package alert_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_base_agent_pkg::*;
  import dv_lib_pkg::*;
  import dv_utils_pkg::*;
  import prim_alert_pkg::*;

  // 2 clock cycles between two alert handshakes, 1 clock cycle to go back to `Idle` state,
  // 1 clock cycle for monitor to detect alert, and 1 for synchronizer skip.
  parameter uint ALERT_B2B_DELAY = 5;

  typedef class alert_agent_cfg;

  typedef enum {
    AlertPingTrans,
    AlertSigTrans,
    AlertIntFail
  } alert_trans_type_e;

  typedef enum {
    AlertPingReceived,
    AlertReceived,
    AlertAckReceived,
    AlertComplete,
    AlertAckComplete
  } alert_handshake_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  `include "alert_seq_item.sv"

  `include "alert_agent_cfg.sv"
  `include "alert_agent_cov.sv"
  `include "alert_base_driver.sv"
  `include "alert_sender_driver.sv"
  `include "alert_receiver_driver.sv"
  `include "alert_sequencer.sv"
  `include "alert_monitor.sv"

  // Sequences
  `include "seq_lib/alert_receiver_base_seq.sv"
  `include "seq_lib/alert_receiver_alert_rsp_seq.sv"
  `include "seq_lib/alert_receiver_ping_seq.sv"
  `include "seq_lib/alert_receiver_seq.sv"
  `include "seq_lib/alert_sender_base_seq.sv"
  `include "seq_lib/alert_sender_ping_rsp_seq.sv"
  `include "seq_lib/alert_sender_seq.sv"

  `include "alert_agent.sv"
endpackage
