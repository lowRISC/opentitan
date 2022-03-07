// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from OTP

`ifndef LC_CTRL_FSM_STATE_REGS_PATH
`define LC_CTRL_FSM_STATE_REGS_PATH \
    tb.dut.u_lc_ctrl_fsm.u_fsm_state_regs.u_state_flop.gen_generic.u_impl_generic.q_o
`endif

`ifndef LC_CTRL_KMAC_FSM_STATE_REGS_PATH
`define LC_CTRL_KMAC_FSM_STATE_REGS_PATH \
    tb.dut.u_lc_ctrl_kmac_if.u_state_regs.u_state_flop.gen_generic.u_impl_generic.q_o
`endif

`ifndef LC_CTRL_STATE_PATH
`define LC_CTRL_STATE_PATH \
    tb.dut.otp_lc_data_i.state
`endif

`ifndef LC_CTRL_COUNT_PATH
`define LC_CTRL_COUNT_PATH \
    tb.dut.otp_lc_data_i.count
`endif

interface lc_ctrl_if (
  input clk,
  input rst_n
);

  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;


  logic tdo_oe;  // TODO: add assertions
  otp_lc_data_t otp_i;
  otp_device_id_t otp_device_id_i = 0;
  otp_device_id_t otp_manuf_state_i = 0;
  lc_token_t hashed_token;
  prim_mubi_pkg::mubi4_t scanmode_i = prim_mubi_pkg::MuBi4False;
  logic scan_rst_ni = 1;
  lc_tx_t lc_dft_en_o;
  lc_tx_t lc_nvm_debug_en_o;
  lc_tx_t lc_hw_debug_en_o;
  lc_tx_t lc_cpu_en_o;
  lc_tx_t lc_creator_seed_sw_rw_en_o;
  lc_tx_t lc_owner_seed_sw_rw_en_o;
  lc_tx_t lc_iso_part_sw_rd_en_o;
  lc_tx_t lc_iso_part_sw_wr_en_o;
  lc_tx_t lc_seed_hw_rd_en_o;
  lc_tx_t lc_keymgr_en_o;
  lc_tx_t lc_escalate_en_o;
  lc_tx_t lc_check_byp_en_o;

  lc_tx_t clk_byp_req_o;
  lc_tx_t clk_byp_ack_i;
  lc_tx_t flash_rma_req_o;
  lc_tx_t flash_rma_ack_i;

  lc_keymgr_div_t keymgr_div_o;
  lc_flash_rma_seed_t flash_rma_seed_o;

  // OTP test signals
  logic [OtpTestCtrlWidth-1:0] otp_vendor_test_ctrl_o;
  logic [OtpTestStatusWidth-1:0] otp_vendor_test_status_i;

  event lc_fsm_state_backdoor_write_ev;
  event lc_fsm_state_backdoor_read_ev;
  event kmac_fsm_state_backdoor_write_ev;
  event kmac_fsm_state_backdoor_read_ev;
  event state_backdoor_write_ev;
  event state_backdoor_read_ev;
  event count_backdoor_write_ev;
  event count_backdoor_read_ev;


  //
  // Whitebox signals - these come from within the RTL
  //

  // Decoded mutex claim signal for JTAG and TL
  logic mutex_claim_jtag;
  logic mutex_claim_tl;

  // Debug signals
  lc_ctrl_env_pkg::lc_ctrl_err_inj_t err_inj;
  lc_ctrl_env_pkg::lc_ctrl_test_phase_e test_phase;
  bit [79:0][7:0] test_sequence_typename;

  task automatic init(lc_state_e lc_state = LcStRaw, lc_cnt_e lc_cnt = LcCnt0,
                      lc_tx_t clk_byp_ack = Off, lc_tx_t flash_rma_ack = Off,
                      logic otp_partition_err = 0, otp_device_id_t otp_device_id = 0,
                      logic otp_lc_data_i_valid = 1, otp_device_id_t otp_manuf_state = 0,
                      logic [OtpTestStatusWidth-1:0] otp_vendor_test_status = 0);
    otp_i.valid             = otp_lc_data_i_valid;
    otp_i.error             = otp_partition_err;
    otp_i.state             = lc_state;
    otp_i.count             = lc_cnt;
    otp_i.test_unlock_token = lc_ctrl_env_pkg::get_random_token();
    otp_i.test_exit_token   = lc_ctrl_env_pkg::get_random_token();
    otp_i.rma_token         = lc_ctrl_env_pkg::get_random_token();
    // TODO: need to randomize this,
    otp_i.secrets_valid     = Off;
    otp_i.test_tokens_valid = On;
    otp_i.rma_token_valid   = On;


    clk_byp_ack_i           = clk_byp_ack;
    flash_rma_ack_i         = flash_rma_ack;

    // Make sure we get a transition
    fork
      begin
        @(posedge clk);
        otp_device_id_i          = otp_device_id;
        otp_manuf_state_i        = otp_manuf_state;
        otp_vendor_test_status_i = otp_vendor_test_status;
      end
    join_none

    release `LC_CTRL_FSM_STATE_REGS_PATH;

  endtask

  task automatic set_clk_byp_ack(lc_tx_t val);
    clk_byp_ack_i = val;
  endtask

  task automatic set_flash_rma_ack(lc_tx_t val);
    flash_rma_ack_i = val;
  endtask

  function automatic void clear_static_signals();
    otp_device_id_i = 0;
    otp_manuf_state_i = 0;
    otp_vendor_test_status_i = 0;
  endfunction

  //
  // The functions below must be static because of the force statement
  //

  // Force lc_ctrl_fsm state registers
  function static void lc_fsm_state_backdoor_write(input logic [FsmStateWidth-1:0] val = 'hdead,
                                                   input int delay_clocks = 0,
                                                   input int force_clocks = 5);
    `dv_info($sformatf("Backdoor write to state registers"))
    fork
      begin : force_state_proc
        repeat (delay_clocks) @(posedge clk);
        ->lc_fsm_state_backdoor_write_ev;
        force `LC_CTRL_FSM_STATE_REGS_PATH = val;
        repeat (force_clocks) @(posedge clk);
        release `LC_CTRL_FSM_STATE_REGS_PATH;
      end : force_state_proc
    join_none
  endfunction

  // Read lc_ctrl_fsm state registers
  function automatic logic [FsmStateWidth-1:0] lc_fsm_state_backdoor_read();
    ->lc_fsm_state_backdoor_read_ev;
    return `LC_CTRL_FSM_STATE_REGS_PATH;
  endfunction

  // Force kmac i/f fsm state registers
  function static void kmac_fsm_state_backdoor_write(
      input logic [lc_ctrl_env_pkg::KMAC_FSM_WIDTH-1:0] val = 'hde, input int delay_clocks = 0,
      input int force_clocks = 5);
    `dv_info($sformatf("Backdoor write to kmac i/f state registers = %h", val))
    fork
      begin : force_state_proc
        repeat (delay_clocks) @(posedge clk);
        ->kmac_fsm_state_backdoor_write_ev;
        force `LC_CTRL_FSM_STATE_REGS_PATH = val;
        repeat (force_clocks) @(posedge clk);
        release `LC_CTRL_FSM_STATE_REGS_PATH;
      end : force_state_proc
    join_none
  endfunction

  // Read  kmac i/f fsm state registers
  function automatic logic [lc_ctrl_env_pkg::KMAC_FSM_WIDTH-1:0] kmac_fsm_state_backdoor_read();
    ->kmac_fsm_state_backdoor_read_ev;
    return `LC_CTRL_FSM_STATE_REGS_PATH;
  endfunction

  // Force OTP state input
  function static void state_backdoor_write(input logic [LcStateWidth-1:0] val = 'hdead,
                                            input int delay_clocks = 0, input int force_clocks = 5);
    `dv_info($sformatf("Backdoor write to OTP state input = %h", val))
    fork
      begin : force_state_proc
        repeat (delay_clocks) @(posedge clk);
        ->state_backdoor_write_ev;
        force `LC_CTRL_STATE_PATH = val;
        repeat (force_clocks) @(posedge clk);
        release `LC_CTRL_STATE_PATH;
      end : force_state_proc
    join_none
  endfunction

  // Read OTP state input
  function automatic logic [LcStateWidth-1:0] state_backdoor_read();
    ->state_backdoor_read_ev;
    return `LC_CTRL_STATE_PATH;
  endfunction

  // Force OTP count input
  function static void count_backdoor_write(input logic [LcCountWidth-1:0] val = 'hdead,
                                            input int delay_clocks = 0, input int force_clocks = 5);
    `dv_info($sformatf("Backdoor write to OTP count input = %h", val))
    fork
      begin : force_count_proc
        repeat (delay_clocks) @(posedge clk);
        ->count_backdoor_write_ev;
        force `LC_CTRL_COUNT_PATH = val;
        repeat (force_clocks) @(posedge clk);
        release `LC_CTRL_COUNT_PATH;
      end : force_count_proc
    join_none
  endfunction

  // Read OTP count input
  function automatic logic [LcCountWidth-1:0] count_backdoor_read();
    ->count_backdoor_read_ev;
    return `LC_CTRL_COUNT_PATH;
  endfunction

  function automatic void set_test_sequence_typename(string name);
    test_sequence_typename = name;
  endfunction

endinterface

`undef LC_CTRL_FSM_STATE_REGS_PATH
`undef LC_CTRL_COUNT_PATH
