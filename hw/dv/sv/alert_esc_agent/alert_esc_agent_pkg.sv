// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package alert_esc_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_lib_pkg::*;
  import dv_utils_pkg::*;
  import prim_alert_pkg::*;
  import prim_esc_pkg::*;

  // 2 clock cycles between two alert handshakes, 1 clock cycle to go back to `Idle` state,
  // 1 clock cycle for monitor to detect alert.
  parameter uint ALERT_B2B_DELAY = 4;

  typedef class alert_esc_seq_item;
  typedef class alert_esc_agent_cfg;

  typedef enum {
    AlertEscPingTrans,
    AlertEscSigTrans,
    AlertEscIntFail
  } alert_esc_trans_type_e;

  typedef enum {
    AlertPingReceived,
    AlertReceived,
    AlertAckReceived,
    AlertComplete,
    AlertAckComplete
  } alert_handshake_e;

  typedef enum {
    EscPingReceived,
    EscReceived,
    EscRespReceived,
    EscComplete,
    EscRespComplete,
    EscIntFail,
    EscRespHi,
    EscRespLo,
    EscRespPing0,
    EscRespPing1
  } esc_handshake_e;

  typedef enum bit [1:0] {
    NoAlertBeforeAfterIntFail  = 'b00,
    HasAlertBeforeIntFailOnly  = 'b01,
    HasAlertAfterIntFailOnly   = 'b10,
    HasAlertBeforeAfterIntFail = 'b11
  } alert_sig_int_err_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // include local files
  `include "alert_esc_seq_item.sv"
  `include "alert_esc_agent_cfg.sv"
  `include "alert_esc_agent_cov.sv"
  `include "alert_esc_base_driver.sv"
  `include "alert_sender_driver.sv"
  `include "alert_receiver_driver.sv"
  `include "esc_sender_driver.sv"
  `include "esc_receiver_driver.sv"
  `include "alert_esc_sequencer.sv"
  `include "alert_esc_base_monitor.sv"
  `include "alert_monitor.sv"
  `include "esc_monitor.sv"
  `include "alert_esc_agent.sv"

  // Sequences
  `include "seq_lib/alert_receiver_base_seq.sv"
  `include "seq_lib/alert_receiver_alert_rsp_seq.sv"
  `include "seq_lib/alert_receiver_seq.sv"
  `include "seq_lib/alert_sender_base_seq.sv"
  `include "seq_lib/alert_sender_ping_rsp_seq.sv"
  `include "seq_lib/alert_sender_seq.sv"
  `include "seq_lib/esc_receiver_base_seq.sv"
  `include "seq_lib/esc_receiver_esc_rsp_seq.sv"

endpackage
