// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence creates lc transition failures such as token mismatch.
class lc_ctrl_errors_vseq extends lc_ctrl_smoke_vseq;

  // Process to handle alerts
  protected process handle_alerts_process;
  // Error injection control
  rand lc_ctrl_err_inj_t err_inj;
  // Invalid lc_state lc_count as a binary representation
  rand lc_state_bin_t invalid_lc_state_bin;
  rand lc_count_bin_t invalid_lc_count_bin;
  rand bit [DecLcStateWidth-1:0] invalid_next_state;
  rand bit [FsmStateWidth-1:0] fsm_state_invert_bits;
  rand bit [LcCountWidth-1:0] fsm_count_invert_bits;
  rand int unsigned fsm_state_err_inj_delay;
  rand int unsigned fsm_state_err_inj_period;
  rand int unsigned fsm_count_err_inj_delay;
  rand int unsigned fsm_count_err_inj_period;

  `uvm_object_utils_begin(lc_ctrl_errors_vseq)
    `uvm_field_int(num_trans, UVM_DEFAULT)
    `uvm_field_int(err_inj, UVM_DEFAULT)
    `uvm_field_int(invalid_lc_state_bin, UVM_DEFAULT)
    `uvm_field_int(invalid_lc_count_bin, UVM_DEFAULT)
    `uvm_field_int(invalid_next_state, UVM_DEFAULT)
    `uvm_field_int(fsm_state_invert_bits, UVM_DEFAULT)
    `uvm_field_int(fsm_state_err_inj_delay, UVM_DEFAULT)
    `uvm_field_int(fsm_state_err_inj_period, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  constraint no_err_rsps_c {
    err_inj.clk_byp_error_rsp == 0;
    err_inj.flash_rma_error_rsp == 0;
  }

  constraint otp_prog_err_c {err_inj.otp_prog_err == 0;}

  constraint token_mismatch_err_c {err_inj.token_mismatch_err == 0;}

  constraint lc_state_failure_c {
    err_inj.state_err == 0;
    err_inj.state_backdoor_err == 0;
    err_inj.count_err == 0;
    err_inj.count_backdoor_err == 0;
  }

  constraint lc_errors_c {err_inj.transition_err == 0;}

  constraint invalid_states_bin_c {
    !(invalid_lc_state_bin inside {ValidLcStatesBin});
    !(invalid_lc_count_bin inside {ValidLcCountsBin});
    !(invalid_next_state inside {ValidDecodedStates});
  }

  constraint fsm_state_invert_bits_c {
    // Just one bit flipped by default
    $onehot(fsm_state_invert_bits);
  }

  constraint fsm_count_invert_bits_c {
    // Just one bit flipped by default
    $onehot(fsm_count_invert_bits);
  }

  constraint fsm_state_err_inj_delay_c {
    fsm_state_err_inj_delay inside {[1 : 5]};
    fsm_state_err_inj_period inside {[2 : 4]};
  }

  constraint fsm_count_err_inj_delay_c {
    fsm_count_err_inj_delay inside {[1 : 5]};
    fsm_count_err_inj_period inside {[2 : 4]};
  }

  virtual task post_start();
    `uvm_info(`gfn, "post_start: Task called for lc_ctrl_errors_vseq", UVM_MEDIUM)

    // Clear all error injection bits so we end with a clean lc_ state, lc_count etc.
    err_inj = 0;

    // trigger dut_init to make sure always on alert is not firing forever
    if (do_apply_reset) begin
      `uvm_info(`gfn, "post_start: calling dut_init", UVM_MEDIUM)
      dut_init();
    end else begin
      `uvm_info(`gfn, "post_start: waiting to be killed", UVM_MEDIUM)
      wait(0);  // wait until upper seq resets and kills this seq
    end
    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
    super.post_start();

  endtask

  task body();
    uvm_reg_data_t rdata;
    logic [FsmStateWidth-1:0] fsm_state;
    num_trans.rand_mode(0);

    fork
      handle_alerts();
    join_none

    run_clk_byp_rsp_nonblocking(err_inj.clk_byp_error_rsp);
    run_flash_rma_rsp_nonblocking(err_inj.flash_rma_error_rsp);

    for (int i = 1; i <= num_trans; i++) begin
      cfg.set_test_phase(LcCtrlIterStart);

      if (i != 1) begin
        `DV_CHECK_RANDOMIZE_FATAL(this)
        dut_init();
      end

      update_err_inj_cfg();

      `uvm_info(`gfn, $sformatf(
                "starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                i,
                num_trans,
                lc_state.name,
                lc_cnt.name
                ), UVM_MEDIUM)

      if ($urandom_range(0, 1)) begin
        csr_rd_check(.ptr(ral.status.ready), .compare_value(1));
      end

      cfg.set_test_phase(LcCtrlDutReady);

      // Invalid fsm state in registers by "backdoor"
      if (err_inj.state_backdoor_err) begin
        fork
          begin
            cfg.clk_rst_vif.wait_clks(fsm_state_err_inj_delay);
            fsm_backdoor_err_inj();
          end
        join_none
      end

      // Invalid fsm state in registers by "backdoor"
      if (err_inj.count_backdoor_err) begin
        fork
          begin
            cfg.clk_rst_vif.wait_clks(fsm_count_err_inj_delay);
            count_backdoor_err_inj();
          end
        join_none
      end

      // SW transition request
      if ((err_inj.state_err || valid_state_for_trans(
              lc_state
          )) && (err_inj.count_err || lc_cnt != LcCnt24)) begin
        lc_ctrl_state_pkg::lc_token_t token_val = get_random_token();
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf(
                  "next_LC_state is %0s, input token is %0h", next_lc_state.name, token_val),
                  UVM_HIGH)

        set_hashed_token();
        sw_transition_req(next_lc_state, token_val);
      end else begin
        // wait at least two clks for scb to finish checking lc outputs
        cfg.clk_rst_vif.wait_clks($urandom_range(10, 2));
      end

      // Allow escalate to be generated if we have received an alert
      cfg.set_test_phase(LcCtrlReadState1);
      // Check count and state before escalate is generated
      rd_lc_state_and_cnt_csrs();

      // Allow escalate to be generated if we have received an alert
      cfg.set_test_phase(LcCtrlEscalate);

      // Wait before re-checking lc_state to allow escalate to be accepted
      cfg.clk_rst_vif.wait_clks(100);
      cfg.set_test_phase(LcCtrlReadState2);
      // Check count and state after escalate is generated
      rd_lc_state_and_cnt_csrs();

      // Sample coverage if enabled
      if (cfg.en_cov) begin
        sample_cov();
      end

    end

    // Clear error injection object so we don't get expect alerts etc.
    cfg.err_inj = 0;

    `uvm_info(`gfn, "body: finished", UVM_MEDIUM)
  endtask : body

  // smoke test will always return valid next_lc_state
  // need to randomize here because associative array's index cannot be a rand input in constraint
  // verilog_format: off - avoid bad formatting
  virtual function void randomize_next_lc_state(dec_lc_state_e curr_lc_state);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_state,
        if (!err_inj.transition_err && !err_inj.state_err) {
          // Valid transition
          next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]};
        } else if (!err_inj.state_err) {
          // Invalid transition
          !(next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]});
        })
  endfunction
  // verilog_format: on - avoid bad formatting

  // This function add otp_program_i's error bit field from the otp_prog_pull_agent device driver.
  // The pushed data length is (num_trans * 2) because for each transaction, we will have two
  // otp_program request at most (one for lc_token and one for lc_state)
  virtual function void add_otp_prog_err_bit();
    repeat (num_trans * 2) begin
      bit err_bit = err_inj.otp_prog_err ? $urandom_range(0, 1) : 0;
      cfg.m_otp_prog_pull_agent_cfg.add_d_user_data(err_bit);
    end
  endfunction

  virtual function void set_hashed_token();
    lc_ctrl_pkg::token_idx_e token_idx = get_exp_token(dec_lc_state(lc_state), next_lc_state);

    // No token for InvalidTokenIdx
    lc_ctrl_state_pkg::lc_token_t tokens_a[NumTokens-1];
    tokens_a[ZeroTokenIdx]       = 0;
    tokens_a[RawUnlockTokenIdx]  = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
    tokens_a[TestUnlockTokenIdx] = cfg.lc_ctrl_vif.otp_i.test_unlock_token;
    tokens_a[TestExitTokenIdx]   = cfg.lc_ctrl_vif.otp_i.test_exit_token;
    tokens_a[RmaTokenIdx]        = cfg.lc_ctrl_vif.otp_i.rma_token;

    if (!err_inj.state_err && !err_inj.count_err) begin
      `DV_CHECK_NE(token_idx, InvalidTokenIdx, $sformatf(
                   "curr_state: %0s, next_state %0s, does not expect InvalidToken",
                   lc_state.name,
                   next_lc_state.name
                   ))
    end

    // Clear the user_data_q here cause previous data might not be used due to some other lc_ctrl
    // error: for example: lc_program error
    cfg.m_otp_token_pull_agent_cfg.clear_d_user_data();
    if (!err_inj.token_mismatch_err) begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(tokens_a[token_idx]);
    end else begin
      // 50% chance to input other token data, 50% chance let push-pull agent drive random data
      if ($urandom_range(0, 1)) begin
        token_idx = token_idx_e'($urandom_range(0, TokenIdxWidth - 2));
        cfg.m_otp_token_pull_agent_cfg.add_d_user_data(tokens_a[token_idx]);
      end
    end
  endfunction

  // Drive OTP input `lc_state` and `lc_cnt`.
  virtual task drive_otp_i(bit rand_otp_i = 1);
    `uvm_info(`gfn, $sformatf("drive_otp_i: started rand_otp_i=%0b err_inj=%p", rand_otp_i, err_inj
              ), UVM_MEDIUM)
    if (rand_otp_i) begin
      if (!err_inj.state_err) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(lc_state)
      end else begin
        // Force invalid state on input
        `uvm_info(`gfn, "drive_otp_i: applying invalid state to otp_i", UVM_MEDIUM)
        lc_state = bin_to_lc_state(invalid_lc_state_bin);
      end

      if (!err_inj.count_err) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_cnt, (lc_state != LcStRaw) -> (lc_cnt != LcCnt0);)
      end else begin
        // Force invalid count on input
        lc_cnt = bin_to_lc_count(invalid_lc_count_bin);
      end

    end else begin
      lc_state = LcStRaw;
      lc_cnt   = LcCnt0;
    end
    cfg.lc_ctrl_vif.init(lc_state, lc_cnt);
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state, bit [TL_DW*4-1:0] token_val);
    bit trigger_alert;
    bit [TL_DW-1:0] status_val;
    csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
    csr_wr(ral.transition_target, next_lc_state);
    foreach (ral.transition_token[i]) begin
      csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
      token_val = token_val >> TL_DW;
    end
    csr_wr(ral.transition_cmd, 'h01);
    cfg.set_test_phase(LcCtrlWaitTransition);
    // Wait for status done or terminal errors
    `DV_SPINWAIT(wait_status(trigger_alert);)
    cfg.set_test_phase(LcCtrlTransitionComplete);
    // always on alert, set time delay to make sure alert triggered for at least for one
    // handshake cycle
    if (trigger_alert) cfg.clk_rst_vif.wait_clks($urandom_range(50, 20));
  endtask

  // Wait for status done or terminal errors
  virtual task wait_status(ref bit expect_alert);
    bit [TL_DW-1:0] status_val;
    bit state_error_exp, state_error_act;
    bit count_error_exp, count_error_act;
    // verilog_format: off - avoid bad formatting
    forever begin
      csr_rd(ral.status, status_val);
      `uvm_info(`gfn, {"wait_status: ", ral.status.sprint(uvm_default_line_printer)}, UVM_MEDIUM)
      if (get_field_val(ral.status.transition_successful, status_val)) break;
      if (get_field_val(ral.status.token_error, status_val)) break;
      if (get_field_val(ral.status.otp_error, status_val) ||
          get_field_val(ral.status.state_error, status_val) ||
          get_field_val(ral.status.bus_integ_error, status_val)) begin
        expect_alert = 1;
        break;
      end
      // verilog_format: on
      // Random delay to next read
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 1));
    end

    // Expected bits
    state_error_exp = cfg.err_inj.state_err || cfg.err_inj.count_err ||
        cfg.err_inj.state_backdoor_err || cfg.err_inj.count_backdoor_err;


    // Actual bits
    state_error_act = get_field_val(ral.status.state_error, status_val);

    // Check status against expected from err_inj
    `DV_CHECK_EQ(state_error_act, state_error_exp)

  endtask

  // checking of these two CSRs are done in scb
  virtual task rd_lc_state_and_cnt_csrs();
    bit [TL_DW-1:0] val;
    csr_rd(ral.lc_state, val);
    csr_rd(ral.lc_transition_cnt, val);
  endtask

  // Update the error injection configuration
  // This is shared with the scoreboard via the environment config object
  virtual function void update_err_inj_cfg();
    cfg.err_inj = err_inj;
    `uvm_info(`gfn, $sformatf("update_err_inj_cfg: %p", cfg.err_inj), UVM_MEDIUM)
  endfunction

  // Sample the coverage for this sequence
  virtual function void sample_cov();
    p_sequencer.cov.sample_cov();
  endfunction

  // Monitor alert events and trigger handling function
  virtual task handle_alerts();
    handle_alerts_process = process::self;
    fork
      forever @(cfg.fatal_prog_error_ev) handle_fatal_prog_error();
      forever @(cfg.fatal_state_error_ev) handle_fatal_state_error();
      forever @(cfg.fatal_bus_integ_error_ev) handle_fatal_bus_integ_error();
    join
  endtask

  // Flip bits in FSM registers
  protected virtual task fsm_backdoor_err_inj();
    logic [FsmStateWidth-1:0] fsm_state;
    fsm_state = cfg.lc_ctrl_vif.fsm_state_backdoor_read();
    fsm_state ^= fsm_state_invert_bits;
    cfg.lc_ctrl_vif.fsm_state_backdoor_write(fsm_state, 0, fsm_state_err_inj_period);
  endtask

  // Flip bits in Count registers
  protected virtual task count_backdoor_err_inj();
    logic [LcCountWidth-1:0] fsm_count;
    fsm_count = cfg.lc_ctrl_vif.fsm_count_backdoor_read();
    fsm_count ^= fsm_count_invert_bits;
    cfg.lc_ctrl_vif.fsm_count_backdoor_write(fsm_count, 0, fsm_count_err_inj_period);
  endtask

  // Send an escalate alert
  protected virtual task send_escalate(int index, int assert_clocks = 1);
    // TODO - replace with calls to escalate agent when driver implemented
    unique case (index)
      0: begin
        cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
        cfg.clk_rst_vif.wait_clks(assert_clocks);
        cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
      end
      1: begin
        cfg.m_esc_scrap_state1_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
        cfg.clk_rst_vif.wait_clks(assert_clocks);
        cfg.m_esc_scrap_state1_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Invalid index %0d", index))
      end
    endcase
  endtask

  // do_print - do a better job of printing structures etc.
  virtual function void do_print(uvm_printer printer);
    super.do_print(printer);
    // err_inj
    printer.print_generic(.name("err_inj"), .type_name("lc_ctrl_err_inj_t"), .size($bits(err_inj)),
                          .value($sformatf("%p", err_inj)));

  endfunction

  // Individual event handlers
  virtual task handle_fatal_prog_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_prog_error: alert received"), UVM_MEDIUM)
    // Only send escalate at correct point of the test
    if (!(cfg.get_test_phase() inside {LcCtrlEscalate, LcCtrlReadState2})) return;
    send_escalate(1, 100);
  endtask

  virtual task handle_fatal_state_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_state_error: alert received"), UVM_MEDIUM)
    // Only send an escalate at the correct part of the test
    if (!(cfg.get_test_phase() inside {LcCtrlEscalate, LcCtrlReadState2})) return;
    send_escalate(0, 100);
  endtask

  virtual task handle_fatal_bus_integ_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_bus_integ_error: alert received"), UVM_MEDIUM)
  endtask

endclass
