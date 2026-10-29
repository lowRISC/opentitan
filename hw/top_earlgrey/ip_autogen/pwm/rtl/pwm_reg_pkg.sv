// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register package: field structs and the register layout as a function of the channel count.

package pwm_reg_pkg;

  // Param list
  // Channel count of the Earl Grey instance, for its DV. The RTL takes the count from the pwm
  // NOutputs parameter instead.
  /* verilator lint_off UNUSEDPARAM */
  parameter int NOutputs = 6;
  /* verilator lint_on UNUSEDPARAM */
  parameter int NumAlerts = 1;

  // Register layout for a block with n channels: ALERT_TEST, REGWEN, CFG, PWM_EN and INVERT,
  // then n each of PWM_PARAM, DUTY_CYCLE and BLINK_PARAM.
  function automatic int unsigned pwm_num_regs(int unsigned n);
    return 5 + 3 * n;
  endfunction

  function automatic int unsigned pwm_block_aw(int unsigned n);
    return $clog2(4 * pwm_num_regs(n));
  endfunction

  function automatic int unsigned pwm_pwm_param_offset();
    return 'h14;
  endfunction

  function automatic int unsigned pwm_duty_cycle_offset(int unsigned n);
    return 'h14 + 4 * n;
  endfunction

  function automatic int unsigned pwm_blink_param_offset(int unsigned n);
    return 'h14 + 8 * n;
  endfunction

  // Alert indices
  typedef enum int {
    AlertFatalFaultIdx = 0
  } pwm_alert_idx_t;

  ////////////////////////////
  // Typedefs for registers //
  ////////////////////////////

  typedef struct packed {
    logic        q;
    logic        qe;
  } pwm_reg2hw_alert_test_reg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } cntr_en;
    struct packed {
      logic [3:0]  q;
      logic        qe;
    } dc_resn;
    struct packed {
      logic [26:0] q;
      logic        qe;
    } clk_div;
  } pwm_reg2hw_cfg_reg_t;

  typedef struct packed {
    logic        q;
    logic        qe;
  } pwm_reg2hw_pwm_en_mreg_t;

  typedef struct packed {
    logic        q;
    logic        qe;
  } pwm_reg2hw_invert_mreg_t;

  typedef struct packed {
    struct packed {
      logic        q;
      logic        qe;
    } blink_en;
    struct packed {
      logic        q;
      logic        qe;
    } htbt_en;
    struct packed {
      logic [15:0] q;
      logic        qe;
    } phase_delay;
  } pwm_reg2hw_pwm_param_mreg_t;

  typedef struct packed {
    struct packed {
      logic [15:0] q;
      logic        qe;
    } b;
    struct packed {
      logic [15:0] q;
      logic        qe;
    } a;
  } pwm_reg2hw_duty_cycle_mreg_t;

  typedef struct packed {
    struct packed {
      logic [15:0] q;
      logic        qe;
    } y;
    struct packed {
      logic [15:0] q;
      logic        qe;
    } x;
  } pwm_reg2hw_blink_param_mreg_t;

  // Reset values for hwext registers and their fields
  parameter logic [0:0] PWM_ALERT_TEST_RESVAL = 1'h 0;
  parameter logic [0:0] PWM_ALERT_TEST_FATAL_FAULT_RESVAL = 1'h 0;

endpackage
