// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// pwrmgr interface.
//
// Samples some internal signals to help coverage collection:
interface pwrmgr_if (
  input logic clk,
  input logic rst_n,
  input logic clk_slow,
  input logic rst_slow_n
);
  import uvm_pkg::*;
  import pwrmgr_env_pkg::*;

  // Ports to the dut side.

  logic                                                        rst_main_n;

  pwrmgr_pkg::pwr_ast_req_t                                    pwr_ast_req;
  pwrmgr_pkg::pwr_ast_rsp_t                                    pwr_ast_rsp;

  pwrmgr_pkg::pwr_rst_req_t                                    pwr_rst_req;
  pwrmgr_pkg::pwr_rst_rsp_t                                    pwr_rst_rsp;

  pwrmgr_pkg::pwr_clk_req_t                                    pwr_clk_req;
  pwrmgr_pkg::pwr_clk_rsp_t                                    pwr_clk_rsp;

  pwrmgr_pkg::pwr_otp_req_t                                    pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t                                    pwr_otp_rsp;

  pwrmgr_pkg::pwr_lc_req_t                                     pwr_lc_req;
  pwrmgr_pkg::pwr_lc_rsp_t                                     pwr_lc_rsp;

  pwrmgr_pkg::pwr_flash_t                                      pwr_flash;

  pwrmgr_pkg::pwrmgr_cpu_t                                     cpu_i;
  pwrmgr_pkg::pwr_cpu_t                                        pwr_cpu;

  lc_ctrl_pkg::lc_tx_t                                         fetch_en;
  lc_ctrl_pkg::lc_tx_t                                         lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t                                         lc_dft_en;

  logic                       [  pwrmgr_reg_pkg::NumWkups-1:0] wakeups_i;
  logic                       [pwrmgr_reg_pkg::NumRstReqs-1:0] rstreqs_i;

  logic                                                        strap;
  logic                                                        low_power;
  rom_ctrl_pkg::pwrmgr_data_t                                  rom_ctrl;

  prim_mubi_pkg::mubi4_t                                       sw_rst_req_i;

  logic                                                        intr_wakeup;

  // Relevant CSR values.
  logic                                                        wakeup_en_regwen;
  logic                       [  pwrmgr_reg_pkg::NumWkups-1:0] wakeup_en;
  logic                       [  pwrmgr_reg_pkg::NumWkups-1:0] wakeup_status;
  logic                                                        wakeup_capture_en;

  logic                       [pwrmgr_reg_pkg::NumRstReqs-1:0] reset_en;
  logic                       [pwrmgr_reg_pkg::NumRstReqs-1:0] reset_en_q;
  logic                       [pwrmgr_reg_pkg::NumRstReqs-1:0] reset_status;

  logic                                                        lowpwr_cfg_wen;
  pwrmgr_reg_pkg::pwrmgr_hw2reg_wake_info_reg_t                wake_info;

  // Internal DUT signals.
`ifndef PATH_TO_DUT
  `define PATH_TO_DUT tb.dut
`endif

  // Slow fsm state.
  pwrmgr_pkg::slow_pwr_state_e slow_state;
  always_comb slow_state = `PATH_TO_DUT.u_slow_fsm.state_q;

  // Fast fsm state.
  pwrmgr_pkg::fast_pwr_state_e fast_state;
  always_comb fast_state = `PATH_TO_DUT.u_fsm.state_q;

  // cfg regwen
  always_comb lowpwr_cfg_wen = `PATH_TO_DUT.lowpwr_cfg_wen;

  // reset status
  always_comb reset_status = {`PATH_TO_DUT.u_reg.reset_status_val_1_qs,
                              `PATH_TO_DUT.u_reg.reset_status_val_0_qs};
  always_comb reset_en_q = {`PATH_TO_DUT.u_reg.reset_en_en_1_qs,
                            `PATH_TO_DUT.u_reg.reset_en_en_0_qs};
  always_comb
    wakeup_en = {
      `PATH_TO_DUT.reg2hw.wakeup_en[5].q,
      `PATH_TO_DUT.reg2hw.wakeup_en[4].q,
      `PATH_TO_DUT.reg2hw.wakeup_en[3].q,
      `PATH_TO_DUT.reg2hw.wakeup_en[2].q,
      `PATH_TO_DUT.reg2hw.wakeup_en[1].q,
      `PATH_TO_DUT.reg2hw.wakeup_en[0].q
    };

  // Wakeup_status ro CSR.
  always_comb
    wakeup_status = {
      `PATH_TO_DUT.hw2reg.wake_status[5].d,
      `PATH_TO_DUT.hw2reg.wake_status[4].d,
      `PATH_TO_DUT.hw2reg.wake_status[3].d,
      `PATH_TO_DUT.hw2reg.wake_status[2].d,
      `PATH_TO_DUT.hw2reg.wake_status[1].d,
      `PATH_TO_DUT.hw2reg.wake_status[0].d
    };

  always_comb wakeup_capture_en = !`PATH_TO_DUT.u_reg.wake_info_capture_dis_qs;
  always_comb wake_info = `PATH_TO_DUT.i_wake_info.info_o;

  logic intr_enable;
  always_comb intr_enable = `PATH_TO_DUT.reg2hw.intr_enable.q;

  logic intr_status;
  always_comb intr_status = `PATH_TO_DUT.reg2hw.intr_state.q;

  // This is only used to determine if an interrupt will be set in case of a reset while in
  // low power.  tryIt is very hard to perdict if the reset or a wakeup happen first, so this
  // signal is used to help instead.
  pwrmgr_pkg::pwrup_cause_e pwrup_cause;
  always_comb pwrup_cause = `PATH_TO_DUT.slow_pwrup_cause;

  // Used to disable assertions once with the first power glitch.
  bit internal_assertion_disabled;

  function automatic void update_ast_main_pok(logic value);
    pwr_ast_rsp.main_pok = value;
  endfunction

  function automatic void update_otp_done(logic value);
    pwr_otp_rsp.otp_done = value;
  endfunction

  function automatic void update_otp_idle(logic value);
    pwr_otp_rsp.otp_idle = value;
  endfunction

  function automatic void update_lc_done(logic value);
    pwr_lc_rsp.lc_done = value;
  endfunction

  function automatic void update_lc_idle(logic value);
    pwr_lc_rsp.lc_idle = value;
  endfunction

  function automatic void update_flash_idle(logic value);
    pwr_flash.flash_idle = value;
  endfunction

  function automatic void update_cpu_sleeping(logic value);
    pwr_cpu.core_sleeping = value;
  endfunction

  function automatic void update_wakeups(logic [pwrmgr_reg_pkg::NumWkups-1:0] wakeups);
    wakeups_i = wakeups;
  endfunction

  function automatic void update_resets(logic [pwrmgr_reg_pkg::NumRstReqs-1:0] resets);
    rstreqs_i = resets;
  endfunction

  function automatic void update_reset_en(
      logic [pwrmgr_reg_pkg::NumRstReqs-1:0] reset_en_value);
    reset_en = reset_en_value;
  endfunction

  function automatic void update_sw_rst_req(prim_mubi_pkg::mubi4_t value);
    sw_rst_req_i = value;
  endfunction

  // Sends a main power glitch and disables a design assertion that trips for power glitches.
  task automatic glitch_power_reset();
    rst_main_n = 1'b0;
    if (!internal_assertion_disabled) begin
      internal_assertion_disabled = 1'b1;
      `uvm_info("pwrmgr_if", "disabling power glitch related SVA", UVM_MEDIUM)
      $assertoff(1, tb.dut.u_slow_fsm.IntRstReq_A);
    end
    repeat (2) @(posedge clk_slow);
    rst_main_n = 1'b1;
  endtask

  // FIXME Move all these initializations to sequences.
  initial begin
    // From AST.
    pwr_ast_rsp = '{default: '0};
    pwr_rst_rsp = '{default: '0};
    pwr_clk_rsp = '{default: '0};
    pwr_otp_rsp = '{default: '0};
    pwr_lc_rsp = '{default: '0};
    pwr_flash = '{default: '0};
    pwr_cpu = pwrmgr_pkg::PWR_CPU_DEFAULT;
    wakeups_i = pwrmgr_pkg::WAKEUPS_DEFAULT;
    rstreqs_i = pwrmgr_pkg::RSTREQS_DEFAULT;
    sw_rst_req_i = prim_mubi_pkg::MuBi4False;
    rom_ctrl = rom_ctrl_pkg::PWRMGR_DATA_DEFAULT;
  end

  clocking slow_cb @(posedge clk_slow);
    input slow_state;
    input pwr_ast_req;
    output pwr_ast_rsp;
  endclocking

  clocking fast_cb @(posedge clk);
    input fast_state;
    input pwr_rst_req;
    output pwr_rst_rsp;
    input pwr_clk_req;
    output pwr_clk_rsp;
    input pwr_lc_req;
    output pwr_lc_rsp;
    input pwr_otp_req;
    output pwr_otp_rsp;
  endclocking
endinterface
