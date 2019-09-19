// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package alert_pkg;

  // these localparams are generated based on the system top-level configuration
  localparam int unsigned NAlerts      = ${n_alerts}; // maximum 252
  localparam int unsigned EscCntDw     = ${esc_cnt_dw}; // maximum 32
  localparam int unsigned AccuCntDw    = ${accu_cnt_dw}; // maximum 32
  localparam logic [31:0] LfsrSeed     = ${lfsr_seed}; // seed for the ping timer (must be nonzero!)
  localparam bit [NAlerts-1:0] AsyncOn = '0; // TODO: make parametric via generator

  // common constants, do not change
  localparam int unsigned N_CLASSES   = 4;
  localparam int unsigned N_ESC_SEV   = 4;
  localparam int unsigned N_PHASES    = 4;
  localparam int unsigned N_LOC_ALERT = 4;

  localparam int unsigned PING_CNT_DW = 24;
  localparam int unsigned PHASE_DW    = $clog2(N_PHASES);
  localparam int unsigned CLASS_DW    = $clog2(N_CLASSES);

  // do not change the phase encoding
  typedef enum logic [2:0] {Idle = 3'b000, Timeout = 3'b001, Terminal = 3'b011,
                            Phase0 = 3'b100, Phase1 = 3'b101, Phase2 = 3'b110,
                            Phase3 = 3'b111} cstate_e;

  // struct containing the current alert handler state
  // can be used to gather crashdump information in HW
  typedef struct packed {
    // alerts
    logic    [NAlerts-1:0]                  alert_cause;     // alert cause bits
    logic    [N_LOC_ALERT-1:0]              loc_alert_cause; // local alert cause bits
    // class state
    logic    [N_CLASSES-1:0][AccuCntDw-1:0] class_accum_cnt; // current accumulator value
    logic    [N_CLASSES-1:0][EscCntDw-1:0]  class_esc_cnt;   // current escalation counter value
    cstate_e [N_CLASSES-1:0]                class_esc_state; // current escalation protocol state
  } alert_crashdump_t;

  // breakout wrapper structs
  typedef struct packed {
    // alerts
    logic    [NAlerts-1:0]                  alert_cause;     // alert cause bits
    logic    [N_LOC_ALERT-1:0]              loc_alert_cause; // local alert cause bits
    // class state
    logic    [N_CLASSES-1:0]                class_trig;      // class trigger
    logic    [N_CLASSES-1:0]                class_esc_trig;  // escalation trigger
    logic    [N_CLASSES-1:0][AccuCntDw-1:0] class_accum_cnt; // current accumulator value
    logic    [N_CLASSES-1:0][EscCntDw-1:0]  class_esc_cnt;   // current escalation counter value
    cstate_e [N_CLASSES-1:0]                class_esc_state; // current escalation protocol state
  } hw2reg_wrap_t;

  typedef struct packed {
    // ping config
    logic                                              config_locked;      // locked -> ping enabled
    logic [PING_CNT_DW-1:0]                            ping_timeout_cyc;   // ping timeout config
    // alert config
    logic [N_LOC_ALERT-1:0]                            loc_alert_en;       // alert enable
    logic [N_LOC_ALERT-1:0][CLASS_DW-1:0]              loc_alert_class;    // alert class config
    logic [NAlerts-1:0]                                alert_en;           // alert enable
    logic [NAlerts-1:0][CLASS_DW-1:0]                  alert_class;        // alert class config
    // class config
    logic [N_CLASSES-1:0]                              class_en;           // enables esc mechanisms
    logic [N_CLASSES-1:0]                              class_clr;          // clears esc/accu
    logic [N_CLASSES-1:0][AccuCntDw-1:0]               class_accum_thresh; // accum esc threshold
    logic [N_CLASSES-1:0][EscCntDw-1:0]                class_timeout_cyc;  // interrupt timeout
    logic [N_CLASSES-1:0][N_PHASES-1:0][EscCntDw-1:0]  class_phase_cyc;    // length of phases 0..3
    logic [N_CLASSES-1:0][N_ESC_SEV-1:0]               class_esc_en;       // esc signal enables
    logic [N_CLASSES-1:0][N_ESC_SEV-1:0][PHASE_DW-1:0] class_esc_map;      // esc signal/phase map
  } reg2hw_wrap_t;

endpackage : alert_pkg

