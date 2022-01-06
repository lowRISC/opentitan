// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from OTP

`ifndef LC_CTRL_FSM_STATE_REGS_PATH
`define LC_CTRL_FSM_STATE_REGS_PATH \
    tb.dut.u_lc_ctrl_fsm.u_fsm_state_regs.u_state_flop.gen_generic.u_impl_generic.d_i
`endif

`ifndef LC_CTRL_FSM_COUNT_REGS_PATH
`define LC_CTRL_FSM_COUNT_REGS_PATH \
    tb.dut.u_lc_ctrl_fsm.u_cnt_regs.gen_generic.u_impl_generic.d_i
`endif


interface lc_ctrl_if (
  input clk,
  input rst_n
);

  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;

  logic                                             tdo_oe;  // TODO: add assertions
  otp_lc_data_t                                     otp_i;
  otp_device_id_t                                   otp_device_id_i;
  otp_device_id_t                                   otp_manuf_state_i;
  lc_token_t                                        hashed_token;

  lc_tx_t                                           lc_dft_en_o;
  lc_tx_t                                           lc_nvm_debug_en_o;
  lc_tx_t                                           lc_hw_debug_en_o;
  lc_tx_t                                           lc_cpu_en_o;
  lc_tx_t                                           lc_creator_seed_sw_rw_en_o;
  lc_tx_t                                           lc_owner_seed_sw_rw_en_o;
  lc_tx_t                                           lc_iso_part_sw_rd_en_o;
  lc_tx_t                                           lc_iso_part_sw_wr_en_o;
  lc_tx_t                                           lc_seed_hw_rd_en_o;
  lc_tx_t                                           lc_keymgr_en_o;
  lc_tx_t                                           lc_escalate_en_o;
  lc_tx_t                                           lc_check_byp_en_o;

  lc_tx_t                                           clk_byp_req_o;
  lc_tx_t                                           clk_byp_ack_i;
  lc_tx_t                                           flash_rma_req_o;
  lc_tx_t                                           flash_rma_ack_i;

  lc_keymgr_div_t                                   keymgr_div_o;
  lc_flash_rma_seed_t                               flash_rma_seed_o;

  event                                             fsm_backdoor_state_write_ev;
  event                                             fsm_backdoor_state_read_ev;
  event                                             fsm_backdoor_count_write_ev;
  event                                             fsm_backdoor_count_read_ev;

  //
  // Whitebox signals - these come from within the RTL
  //

  // Decoded mutex claim signal for JTAG and TL
  logic                                             mutex_claim_jtag;
  logic                                             mutex_claim_tl;

  // Debug signals
  lc_ctrl_env_pkg::lc_ctrl_err_inj_t                err_inj;
  lc_ctrl_env_pkg::lc_ctrl_test_phase_e             test_phase;
  bit                                   [79:0][7:0] test_sequence_typename;

  task automatic init(lc_state_e lc_state = LcStRaw, lc_cnt_e lc_cnt = LcCnt0,
                      lc_tx_t clk_byp_ack = Off, lc_tx_t flash_rma_ack = Off,
                      logic otp_partition_err = 0);
    otp_i.valid             = 1;
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

    otp_device_id_i         = 0;
    otp_manuf_state_i       = 0;

    clk_byp_ack_i           = clk_byp_ack;
    flash_rma_ack_i         = flash_rma_ack;

    release `LC_CTRL_FSM_STATE_REGS_PATH;
  endtask

  task automatic set_clk_byp_ack(lc_tx_t val);
    clk_byp_ack_i = val;
  endtask

  task automatic set_flash_rma_ack(lc_tx_t val);
    flash_rma_ack_i = val;
  endtask

  // This must be static because of the force statement
  function static void fsm_state_backdoor_write(input logic [FsmStateWidth-1:0] val = 'hdead,
                                                input int delay_clocks = 0,
                                                input int force_clocks = 5);
    `dv_info($sformatf("Backdoor write to state registers"))
    fork
      begin : force_state_proc
        repeat (delay_clocks) @(posedge clk);
        ->fsm_backdoor_state_write_ev;
        force `LC_CTRL_FSM_STATE_REGS_PATH = val;
        repeat (force_clocks) @(posedge clk);
        release `LC_CTRL_FSM_STATE_REGS_PATH;
      end : force_state_proc
    join_none
  endfunction

  function automatic logic [FsmStateWidth-1:0] fsm_state_backdoor_read();
    ->fsm_backdoor_state_read_ev;
    return `LC_CTRL_FSM_STATE_REGS_PATH;
  endfunction

  // This must be static because of the force statement
  function static void fsm_count_backdoor_write(input logic [LcCountWidth-1:0] val = 'hdead,
                                                input int delay_clocks = 0,
                                                input int force_clocks = 5);
    `dv_info($sformatf("Backdoor write to state registers"))
    fork
      begin : force_count_proc
        repeat (delay_clocks) @(posedge clk);
        ->fsm_backdoor_count_write_ev;
        force `LC_CTRL_FSM_COUNT_REGS_PATH = val;
        repeat (force_clocks) @(posedge clk);
        release `LC_CTRL_FSM_COUNT_REGS_PATH;
      end : force_count_proc
    join_none
  endfunction

  function automatic logic [LcCountWidth-1:0] fsm_count_backdoor_read();
    ->fsm_backdoor_count_read_ev;
    return `LC_CTRL_FSM_COUNT_REGS_PATH;
  endfunction

  function automatic set_test_sequence_typename(string name);
    test_sequence_typename = name;
  endfunction

endinterface

`undef LC_CTRL_FSM_STATE_REGS_PATH
`undef LC_CTRL_FSM_COUNT_REGS_PATH
