// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Package
//

package pwrmgr_pkg;

  // global constant
  parameter int ALWAYS_ON_DOMAIN = 0;

  // variables referenced by other modules / packages
  parameter int PowerDomains = 2; // this needs to be a topgen populated number, or from topcfg?

  // variables referenced only by pwrmgr
  localparam int TotalWakeWidth = pwrmgr_reg_pkg::NumWkups + 2; // Abort and fall through are added

  //// The following structs should eventually be relocted to other modules
  //typedef enum logic [1:0] {
  //  DiffValid = 2'b10,
  //  DiffInvalid = 2'b01
  //} pwrmgr_diff_e;

  // pwrmgr to ast
  typedef struct packed {
    logic main_pd_n;
    logic pwr_clamp;
    logic slow_clk_en;
    logic core_clk_en;
    logic io_clk_en;
    logic usb_clk_en;
  } pwr_ast_req_t;

  typedef struct packed {
    logic slow_clk_val;
    logic core_clk_val;
    logic io_clk_val;
    logic usb_clk_val;
    logic main_pok;
  } pwr_ast_rsp_t;

  // default value of pwr_ast_rsp (for dangling ports)
  parameter pwr_ast_rsp_t PWR_AST_RSP_DEFAULT = '{
    slow_clk_val: 1'b1,
    core_clk_val: 1'b1,
    io_clk_val: 1'b1,
    usb_clk_val: 1'b1,
    main_pok: 1'b1
  };

  parameter pwr_ast_rsp_t PWR_AST_RSP_SYNC_DEFAULT = '{
    slow_clk_val: 1'b0,
    core_clk_val: 1'b0,
    io_clk_val: 1'b0,
    usb_clk_val: 1'b0,
    main_pok: 1'b0
  };

  // reasons for pwrmgr reset reset
  typedef enum logic [1:0] {
    ResetNone = 0,     // there is no reset
    LowPwrEntry = 1,   // reset is caused by low power entry
    HwReq = 2,         // reset is caused by peripheral reset requests
    ResetUndefined = 3 // this should never happen outside of POR
  } reset_cause_e;

  // pwrmgr to rstmgr
  typedef struct packed {
    logic [PowerDomains-1:0] rst_lc_req;
    logic [PowerDomains-1:0] rst_sys_req;
    logic [pwrmgr_reg_pkg::NumRstReqs:0] rstreqs;
    reset_cause_e reset_cause;
  } pwr_rst_req_t;

  // rstmgr to pwrmgr
  typedef struct packed {
    logic [PowerDomains-1:0] rst_lc_src_n;
    logic [PowerDomains-1:0] rst_sys_src_n;
  } pwr_rst_rsp_t;

  // default value (for dangling ports)
  parameter pwr_rst_rsp_t PWR_RST_RSP_DEFAULT = '{
    rst_lc_src_n: {PowerDomains{1'b1}},
    rst_sys_src_n: {PowerDomains{1'b1}}
  };

  // pwrmgr to clkmgr
  typedef struct packed {
    logic ip_clk_en;
  } pwr_clk_req_t;

  // clkmgr to powrmgr
  typedef struct packed {
    logic clk_status;
  } pwr_clk_rsp_t;

  // pwrmgr to otp
  typedef struct packed {
    logic otp_init;
  } pwr_otp_req_t;

  // otp to pwrmgr
  typedef struct packed {
    logic otp_done;
    logic otp_idle;
  } pwr_otp_rsp_t;

  // default value (for dangling ports)
  parameter pwr_otp_rsp_t PWR_OTP_RSP_DEFAULT = '{
    otp_done: 1'b1,
    otp_idle: 1'b1
  };

  // pwrmgr to lifecycle
  typedef struct packed {
    logic lc_init;
  } pwr_lc_req_t;

  // lifecycle to pwrmgr
  typedef struct packed {
    logic lc_done;
    logic lc_idle;
  } pwr_lc_rsp_t;

  // default value (for dangling ports)
  parameter pwr_lc_rsp_t PWR_LC_RSP_DEFAULT = '{
    lc_done: 1'b1,
    lc_idle: 1'b1
  };

  // flash to pwrmgr
  typedef struct packed {
    logic flash_init;
  } pwr_flash_req_t;

  typedef struct packed {
    logic flash_done;
    logic flash_idle;
  } pwr_flash_rsp_t;

  // default value (for dangling ports)
  parameter pwr_flash_req_t PWR_FLASH_REQ_DEFAULT = '{
    flash_init: 1'b1
  };

  parameter pwr_flash_rsp_t PWR_FLASH_RSP_DEFAULT = '{
    flash_done: 1'b1,
    flash_idle: 1'b1
  };

  // processor to pwrmgr
  typedef struct packed {
    logic core_sleeping;
  } pwr_cpu_t;

  // default value (for dangling ports)
  parameter pwr_cpu_t PWR_CPU_DEFAULT = '{
    core_sleeping: 1'b0
  };

  // default value (for dangling ports)
  parameter int WAKEUPS_DEFAULT = '0;
  parameter int RSTREQS_DEFAULT = '0;

  // peripherals to pwrmgr
  typedef struct packed {
    logic [pwrmgr_reg_pkg::NumWkups-1:0] wakeups;
    // reset requests include external requests + escalation reset
    logic [pwrmgr_reg_pkg::NumRstReqs:0] rstreqs;
  } pwr_peri_t;

  // power-up causes
  typedef enum logic [1:0] {
    Por   = 2'h0,
    Wake  = 2'h1,
    Reset = 2'h2
  } pwrup_cause_e;

  // low power hints
  typedef enum logic {
    None     = 1'b0,
    LowPower = 1'b1
  } low_power_hint_e;

  // fast fsm state enum
  typedef enum logic [4:0] {
    FastPwrStateLowPower,
    FastPwrStateEnableClocks,
    FastPwrStateReleaseLcRst,
    FastPwrStateOtpInit,
    FastPwrStateLcInit,
    FastPwrStateStrap,
    FastPwrStateFlashInit,
    FastPwrStateAckPwrUp,
    FastPwrStateActive,
    FastPwrStateDisClks,
    FastPwrStateFallThrough,
    FastPwrStateNvmIdleChk,
    FastPwrStateLowPowerPrep,
    FastPwrStateNvmShutDown,
    FastPwrStateResetPrep,
    FastPwrStateReqPwrDn
  } fast_pwr_state_e;

  // slow fsm state enum
  typedef enum logic [3:0] {
    SlowPwrStateReset,
    SlowPwrStateLowPower,
    SlowPwrStateMainPowerOn,
    SlowPwrStateClocksOn,
    SlowPwrStateReqPwrUp,
    SlowPwrStateIdle,
    SlowPwrStateAckPwrDn,
    SlowPwrStateClocksOff,
    SlowPwrStateMainPowerOff
  } slow_pwr_state_e;

endpackage // pwrmgr_pkg
