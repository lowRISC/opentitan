// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package alert_pkg;

  // these localparams are generated based on the system top-level configuration
  localparam int unsigned      NAlerts   = alert_handler_reg_pkg::NAlerts;   // maximum 252
  localparam int unsigned      EscCntDw  = alert_handler_reg_pkg::EscCntDw;  // maximum 32
  localparam int unsigned      AccuCntDw = alert_handler_reg_pkg::AccuCntDw; // maximum 32
  localparam int unsigned      NLpg      = alert_handler_reg_pkg::NLpg;
  localparam int unsigned      NLpgWidth = alert_handler_reg_pkg::NLpgWidth;
  localparam logic [NAlerts-1:0][NLpgWidth-1:0] LpgMap = alert_handler_reg_pkg::LpgMap;
  // enable async transitions for specific RX/TX pairs
  localparam bit [NAlerts-1:0] AsyncOn   = alert_handler_reg_pkg::AsyncOn;

  // common constants, do not change
  localparam int unsigned N_CLASSES   = alert_handler_reg_pkg::N_CLASSES;
  localparam int unsigned N_ESC_SEV   = alert_handler_reg_pkg::N_ESC_SEV;
  localparam int unsigned N_PHASES    = alert_handler_reg_pkg::N_PHASES;
  localparam int unsigned N_LOC_ALERT = alert_handler_reg_pkg::N_LOC_ALERT;

  localparam int unsigned PING_CNT_DW = alert_handler_reg_pkg::PING_CNT_DW;
  localparam int unsigned PHASE_DW    = alert_handler_reg_pkg::PHASE_DW;
  localparam int unsigned CLASS_DW    = alert_handler_reg_pkg::CLASS_DW;

  // do not change the phase encoding
  typedef enum logic [2:0] {Idle = 3'b000, Timeout = 3'b001, Terminal = 3'b011,
                            Phase0 = 3'b100, Phase1 = 3'b101, Phase2 = 3'b110,
                            Phase3 = 3'b111, FsmError = 3'b010} cstate_e;

  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 32 --seed 2700182644
  localparam int LfsrWidth = 32;
  typedef logic [LfsrWidth-1:0]                        lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  localparam lfsr_seed_t RndCnstLfsrSeedDefault = 32'he96064e5;
  localparam lfsr_perm_t RndCnstLfsrPermDefault =
      160'hebd1e5d4a1cee5afdb866a9c7a0278b899020d31;

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

  // Default for dangling connection
  parameter alert_crashdump_t ALERT_CRASHDUMP_DEFAULT = '{
    alert_cause: '0,
    loc_alert_cause: '0,
    class_accum_cnt: '0,
    class_esc_cnt: '0,
    class_esc_state: {N_CLASSES{Idle}}
  };

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
    // aggregated shadow reg errors (trigger internal alerts)
    logic                                              shadowed_err_update;
    logic                                              shadowed_err_storage;
    // ping config
    logic                                              ping_enable;        // ping timer enable
    logic [PING_CNT_DW-1:0]                            ping_timeout_cyc;   // ping timeout config
    logic [NAlerts-1:0]                                alert_ping_en;      // ping enable for alerts
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
    // determines when to latch the crashdump output.
    logic [N_CLASSES-1:0][PHASE_DW-1:0]                class_crashdump_phase;
  } reg2hw_wrap_t;

endpackage : alert_pkg


