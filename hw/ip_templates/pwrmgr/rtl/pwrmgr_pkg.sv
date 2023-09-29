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

  parameter int NumSwRstReq = 1;

  // position of escalation request
  parameter int HwResetWidth = pwrmgr_reg_pkg::NumRstReqs +
                               pwrmgr_reg_pkg::NumIntRstReqs +
                               pwrmgr_reg_pkg::NumDebugRstReqs;
  parameter int TotalResetWidth = HwResetWidth + NumSwRstReq;
  parameter int ResetSwReqIdx = TotalResetWidth - 1;

  // pwrmgr to ast
  typedef struct packed {
    logic main_pd_n;
    logic pwr_clamp_env;
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

  // reasons for pwrmgr reset
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
    logic [HwResetWidth-1:0] rstreqs;
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
    logic main_ip_clk_en;
    logic io_ip_clk_en;
    logic usb_ip_clk_en;
  } pwr_clk_req_t;

  // clkmgr to pwrmgr
  typedef struct packed {
    logic main_status;
    logic io_status;
    logic usb_status;
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

  typedef struct packed {
    logic flash_idle;
  } pwr_flash_t;

  parameter pwr_flash_t PWR_FLASH_DEFAULT = '{
    flash_idle: 1'b1
  };

  // processor to pwrmgr
  typedef struct packed {
    logic core_sleeping;
  } pwr_cpu_t;

  // cpu reset requests and status
  typedef struct packed {
    logic ndmreset_req;
  } pwrmgr_cpu_t;

  // exported resets

  // default value for pwrmgr_ast_rsp_t (for dangling ports)
  parameter pwrmgr_cpu_t PWRMGR_CPU_DEFAULT = '{
    ndmreset_req: '0
  };

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
    logic [TotalResetWidth-1:0] rstreqs;
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
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 19 -n 12 \
  //      -s 3096160381 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: ||||||||||||||||| (30.99%)
  //  6: |||||||||||||||||||| (35.09%)
  //  7: ||||||||| (15.79%)
  //  8: |||||| (10.53%)
  //  9: ||| (5.85%)
  // 10: | (1.75%)
  // 11: --
  // 12: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 10
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 10
  //
  localparam int FastPwrStateWidth = 12;
  typedef enum logic [FastPwrStateWidth-1:0] {
    FastPwrStateLowPower     = 12'b000000110111,
    FastPwrStateEnableClocks = 12'b101011001110,
    FastPwrStateReleaseLcRst = 12'b100111000000,
    FastPwrStateOtpInit      = 12'b111110100010,
    FastPwrStateLcInit       = 12'b101001010011,
    FastPwrStateStrap        = 12'b110000111010,
    FastPwrStateAckPwrUp     = 12'b000010101000,
    FastPwrStateRomCheckDone = 12'b010111110011,
    FastPwrStateRomCheckGood = 12'b010000000100,
    FastPwrStateActive       = 12'b001101100100,
    FastPwrStateDisClks      = 12'b001110010101,
    FastPwrStateFallThrough  = 12'b011011010000,
    FastPwrStateNvmIdleChk   = 12'b100101111001,
    FastPwrStateLowPowerPrep = 12'b010110001111,
    FastPwrStateNvmShutDown  = 12'b001100001010,
    FastPwrStateResetPrep    = 12'b011001101111,
    FastPwrStateResetWait    = 12'b111111111100,
    FastPwrStateReqPwrDn     = 12'b111010001001,
    FastPwrStateInvalid      = 12'b110101010110
  } fast_pwr_state_e;

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 12 -n 10 \
  //      -s 1726685338 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (54.55%)
  //  6: |||||||||||||||| (45.45%)
  //  7: --
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 8
  //
  localparam int SlowPwrStateWidth = 10;
  typedef enum logic [SlowPwrStateWidth-1:0] {
    SlowPwrStateReset = 10'b0000100010,
    SlowPwrStateLowPower = 10'b1011000111,
    SlowPwrStateMainPowerOn = 10'b0110101111,
    SlowPwrStatePwrClampOff = 10'b0110010001,
    SlowPwrStateClocksOn = 10'b1010111100,
    SlowPwrStateReqPwrUp = 10'b0011011010,
    SlowPwrStateIdle = 10'b1111100000,
    SlowPwrStateAckPwrDn = 10'b0001110101,
    SlowPwrStateClocksOff = 10'b1101111011,
    SlowPwrStatePwrClampOn = 10'b0101001100,
    SlowPwrStateMainPowerOff = 10'b1000001001,
    SlowPwrStateInvalid = 10'b1100010110
  } slow_pwr_state_e;

endpackage // pwrmgr_pkg
