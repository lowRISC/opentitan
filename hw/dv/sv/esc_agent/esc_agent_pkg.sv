// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package esc_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_base_agent_pkg::*;
  import dv_lib_pkg::*;
  import dv_utils_pkg::*;
  import prim_esc_pkg::*;

  typedef enum {
    EscPingTrans,
    EscSigTrans,
    EscIntFail
  } esc_trans_type_e;

  typedef enum {
    EscPingReceived,
    EscReceived,
    EscRespReceived,
    EscComplete,
    EscRespComplete,
    EscHSIntFail,
    EscRespHi,
    EscRespLo,
    EscRespPing0,
    EscRespPing1
  } esc_handshake_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  `include "esc_seq_item.sv"

  `include "esc_agent_cfg.sv"
  `include "esc_agent_cov.sv"
  `include "esc_sender_driver.sv"
  `include "esc_receiver_driver.sv"
  `include "esc_sequencer.sv"
  `include "esc_monitor.sv"

  `include "seq_lib/esc_receiver_base_seq.sv"
  `include "seq_lib/esc_receiver_esc_rsp_seq.sv"

  `include "esc_agent.sv"
endpackage
