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
  rand bit [FsmStateWidth-1:0] lc_fsm_state_invert_bits;
  rand bit [KMAC_FSM_WIDTH-1:0] kmac_fsm_state_invert_bits;
  rand bit [LcCountWidth-1:0] count_invert_bits;
  rand bit [LcStateWidth-1:0] state_invert_bits;
  rand int unsigned lc_fsm_state_err_inj_delay;
  rand int unsigned lc_fsm_state_err_inj_period;
  rand int unsigned kmac_fsm_state_err_inj_delay;
  rand int unsigned kmac_fsm_state_err_inj_period;
  rand int unsigned state_err_inj_delay;
  rand int unsigned state_err_inj_period;
  rand int unsigned count_err_inj_delay;
  rand int unsigned count_err_inj_period;

  rand int unsigned security_escalation_err_inj_delay;
  rand bit [1:0] security_escalation_err_inj_channels;


  bit fatal_prog_alert_received;
  bit fatal_state_alert_received;
  bit fatal_bus_integ_alert_received;
  bit assertions_disabled;


  `uvm_object_utils_begin(lc_ctrl_errors_vseq)
    `uvm_field_int(num_trans, UVM_DEFAULT)
    `uvm_field_int(err_inj, UVM_DEFAULT)
    `uvm_field_int(invalid_lc_state_bin, UVM_DEFAULT)
    `uvm_field_int(invalid_lc_count_bin, UVM_DEFAULT)
    `uvm_field_int(invalid_next_state, UVM_DEFAULT)
    `uvm_field_int(lc_fsm_state_invert_bits, UVM_DEFAULT)
    `uvm_field_int(lc_fsm_state_err_inj_delay, UVM_DEFAULT)
    `uvm_field_int(lc_fsm_state_err_inj_period, UVM_DEFAULT)
  `uvm_object_utils_end
  `uvm_object_new

  constraint otp_prog_err_c {err_inj.otp_prog_err == 0;}

  constraint post_trans_c {err_inj.post_trans_err == 0;}

  constraint lc_state_failure_c {
    err_inj.state_err == 0;
    err_inj.state_illegal_err == 0;
    err_inj.state_backdoor_err == 0;
    err_inj.count_err == 0;
    err_inj.count_illegal_err == 0;
    err_inj.count_backdoor_err == 0;
    err_inj.lc_fsm_backdoor_err == 0;
    err_inj.kmac_fsm_backdoor_err == 0;
    err_inj.otp_lc_data_i_valid_err == 0;
  }

  constraint lc_errors_c {
    err_inj.transition_err == 0;
    err_inj.transition_count_err == 0;
    err_inj.clk_byp_error_rsp == 0;
    err_inj.flash_rma_error_rsp == 0;
    err_inj.token_mismatch_err == 0;
    err_inj.token_response_err == 0;
    err_inj.token_invalid_err == 0;
    err_inj.otp_partition_err == 0;
  }

  constraint security_escalation_c {
    err_inj.security_escalation_err == 0;
    security_escalation_err_inj_delay == 0;
    security_escalation_err_inj_channels == 0;
  }

  constraint invalid_states_bin_c {
    !(invalid_lc_state_bin inside {ValidLcStatesBin});
    !(invalid_lc_count_bin inside {ValidLcCountsBin});
    !(invalid_next_state inside {ValidDecodedStates});
  }

  constraint lc_fsm_state_invert_bits_c {$onehot(lc_fsm_state_invert_bits);}

  constraint kmac_fsm_state_invert_bits_c {$onehot(kmac_fsm_state_invert_bits);}

  constraint count_invert_bits_c {$onehot(count_invert_bits);}

  constraint state_invert_bits_c {$onehot(state_invert_bits);}

  constraint lc_fsm_state_err_inj_delay_c {
    lc_fsm_state_err_inj_delay inside {[1 : 5]};
    lc_fsm_state_err_inj_period inside {[2 : 4]};

  }

  constraint kmac_fsm_state_err_inj_delay_c {
    kmac_fsm_state_err_inj_delay inside {[1 : 5]};
    kmac_fsm_state_err_inj_period inside {[2 : 4]};
  }

  constraint state_err_inj_delay_c {
    state_err_inj_delay inside {[1 : 5]};
    state_err_inj_period inside {[2 : 4]};
  }

  constraint count_err_inj_delay_c {
    count_err_inj_delay inside {[1 : 5]};
    count_err_inj_period inside {[2 : 4]};
  }

  virtual task post_start();
    `uvm_info(`gfn, "post_start: Task called for lc_ctrl_errors_vseq", UVM_MEDIUM)

    // Clear all error injection bits so we end with a clean lc_ state, lc_count etc.
    err_inj = 0;
    update_err_inj_cfg();

    // Clear assertions disabled flag
    assertions_disabled = 0;

    // trigger dut_init to make sure always on alert is not firing forever
    if (do_apply_reset) begin
      `uvm_info(`gfn, "post_start: calling dut_init", UVM_MEDIUM)
      dut_init();
    end else begin
      `uvm_info(`gfn, "post_start: waiting to be killed", UVM_MEDIUM)
      wait(0);  // wait until upper seq resets and kills this seq
    end

    // Reenable assertions before next sequence
    `DV_ASSERT_CTRL_REQ("OtpProgH_DataStableWhenBidirectionalAndReq_A", 1)
    `DV_ASSERT_CTRL_REQ("OtpProgReqHighUntilAck_A", 1)
    `DV_ASSERT_CTRL_REQ("OtpProgAckAssertedOnlyWhenReqAsserted_A", 1)
    `DV_ASSERT_CTRL_REQ("KmacIfSyncReqAckAckNeedsReq", 1)

    // Kill sub processes
    disable handle_alerts;
    disable handle_escalate;
    disable run_clk_byp_rsp_nonblocking;
    disable run_flash_rma_rsp_nonblocking;

    // Make sure OTP response queue is cleared
    cfg.m_otp_prog_pull_agent_cfg.clear_d_user_data();
    super.post_start();
  endtask

  virtual task pre_start();
    // Align cfg.err_inj with the sequence before body starts
    update_err_inj_cfg();
    super.pre_start();
  endtask

  task body();
    uvm_reg_data_t rdata;
    logic [FsmStateWidth-1:0] fsm_state;

    update_err_inj_cfg();

    fork
      handle_alerts();
      handle_escalate();
    join_none

    run_clk_byp_rsp_nonblocking(err_inj.clk_byp_error_rsp);
    run_flash_rma_rsp_nonblocking(err_inj.flash_rma_error_rsp);

    //
    // Check OTP read only regs
    //
    read_otp_csrs();


    for (int i = 1; i <= num_trans; i++) begin
      cfg.set_test_phase(LcCtrlIterStart);

      if (i != 1) begin
        `DV_CHECK_RANDOMIZE_FATAL(this)
        update_err_inj_cfg();
        dut_init();
      end
      cfg.set_test_phase(LcCtrlDutInitComplete);

      `uvm_info(`gfn, $sformatf(
                "starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s err_inj=%p",
                i,
                num_trans,
                lc_state.name,
                lc_cnt.name,
                err_inj
                ), UVM_MEDIUM)

      // If otp_lc_data_i.valid is not driven we expect to constantly
      // read not ready
      if (err_inj.otp_lc_data_i_valid_err) begin
        // Check for lockup on TL interface
        `DV_SPINWAIT(repeat(10) begin
              csr_rd_check(.ptr(ral.status.ready), .compare_value(0),
                  .err_msg(called_from(`__FILE__, `__LINE__)));
            end)
        // Sample coverage if enabled
        sample_cov();
        // End this iteration
        continue;
      end

      // Randomly check for ready - but not when a non transition state
      // or an illegal state will be driven via the OTP
      if ($urandom_range(0, 1)) begin
        if (valid_state_for_trans(
                lc_state
            ) && !err_inj.state_err && !err_inj.count_err && !err_inj.state_illegal_err &&
                !err_inj.count_illegal_err) begin
          csr_rd_check(.ptr(ral.status.ready), .compare_value(1),
                       .err_msg(called_from(`__FILE__, `__LINE__)));
        end else begin
          // We expect ready to be zero when a bad state is driven
          csr_rd_check(.ptr(ral.status.ready), .compare_value(0),
                       .err_msg(called_from(`__FILE__, `__LINE__)));
        end
      end

      cfg.set_test_phase(LcCtrlDutReady);

      // Invalid LC fsm state in registers by "backdoor"
      if (err_inj.lc_fsm_backdoor_err) begin
        fork
          begin
            cfg.clk_rst_vif.wait_clks(lc_fsm_state_err_inj_delay);
            lc_fsm_backdoor_err_inj();
          end
        join_none
      end

      // Invalid kmac state in registers by "backdoor"
      if (err_inj.kmac_fsm_backdoor_err) begin
        fork
          begin
            cfg.clk_rst_vif.wait_clks(kmac_fsm_state_err_inj_delay);
            kmac_fsm_backdoor_err_inj();
          end
        join_none
      end

      // Invalid OTP state by "backdoor"
      if (err_inj.state_backdoor_err) begin
        fork
          begin
            cfg.clk_rst_vif.wait_clks(state_err_inj_delay);
            state_backdoor_err_inj();
          end
        join_none
      end

      // Invalid OTP count by "backdoor"
      if (err_inj.count_backdoor_err) begin
        fork
          begin
            cfg.clk_rst_vif.wait_clks(count_err_inj_delay);
            count_backdoor_err_inj();
          end
        join_none
      end

      // SW transition request
      // verilog_format: off - avoid bad formatting
      if ((err_inj.state_err || valid_state_for_trans(lc_state)) &&
          (err_inj.count_err || err_inj.transition_count_err ||
          (lc_cnt != LcCnt24 && lc_state != LcStScrap))) begin
        lc_ctrl_state_pkg::lc_token_t token_val = get_random_token();
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf(
                  "next_LC_state is %0s, input token is %0h", next_lc_state.name, token_val),
                  UVM_HIGH)
        set_hashed_token();
        set_otp_prog_rsp();
        cfg.set_test_phase(LcCtrlWaitTransition);
        sw_transition_req(next_lc_state, token_val);
        cfg.set_test_phase(LcCtrlTransitionComplete);
      end else begin
        cfg.set_test_phase(LcCtrlBadNextState);
        // wait at least two clks for scb to finish checking lc outputs
        cfg.clk_rst_vif.wait_clks($urandom_range(10, 2));
      end
      // verilog_format: on

      // Allow volatile registers to settle
      cfg.clk_rst_vif.wait_clks($urandom_range(15, 10));

      cfg.set_test_phase(LcCtrlReadState1);
      // Check count and state before escalate is generated
      // Skip this if we are injecting clock bypass error responses as the KMAC
      // may or may not respond leaving the FSM stuck in TokenHashSt
      if (!err_inj.clk_byp_error_rsp) rd_lc_state_and_cnt_csrs();
      else begin
        `uvm_info(`gfn, "Skipped read of lc state & lc_count because err_inj.clk_byp_error_rsp = 1",
                  UVM_MEDIUM)
        cfg.clk_rst_vif.wait_clks($urandom_range(15, 10));
      end

      // Allow escalate to be generated if we have received an alert
      cfg.set_test_phase(LcCtrlEscalate);

      // Wait before re-checking lc_state to allow escalate to be accepted
      cfg.clk_rst_vif.wait_clks($urandom_range(150, 100));
      cfg.set_test_phase(LcCtrlReadState2);
      // Check count and state after escalate is generated
      rd_lc_state_and_cnt_csrs();

      cfg.set_test_phase(LcCtrlPostTransition);

      // Attempt a second transition post transition if enabled
      // verilog_format: off - avoid bad formatting
      if (err_inj.post_trans_err) begin
        `uvm_info(`gfn, "Attempting second transition post transition", UVM_LOW)
        `DV_CHECK_RANDOMIZE_FATAL(this)
        // Clear all error injections except post_trans_err
        err_inj = '{post_trans_err: 1, default: 0};
        // SW transition request
        if ((err_inj.state_err || valid_state_for_trans(lc_state)) &&
            (err_inj.count_err || err_inj.transition_count_err || lc_cnt != LcCnt24)) begin
          lc_ctrl_state_pkg::lc_token_t token_val = get_random_token();
          randomize_next_lc_state(dec_lc_state(lc_state));
          set_hashed_token();
          set_otp_prog_rsp();
          sw_transition_req(next_lc_state, token_val);
        end else begin
          // wait at least two clks for scb to finish checking lc outputs
          cfg.clk_rst_vif.wait_clks($urandom_range(10, 2));
        end
        cfg.set_test_phase(LcCtrlPostTransTransitionComplete);
      end
      // verilog_format: on

      // Sample coverage if enabled
      sample_cov();

    end
    // Clear error injection object so we don't get alerts etc.
    cfg.err_inj = 0;

    `uvm_info(`gfn, "body: finished", UVM_MEDIUM)
  endtask : body

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    // Make sure escalates and alert flags are cleared
    clear_escalate(0);
    clear_escalate(1);
    fatal_prog_alert_received = 0;
    fatal_state_alert_received = 0;
    fatal_bus_integ_alert_received = 0;

    // Disable assertions depending on error injection
    if (err_inj.clk_byp_error_rsp || err_inj.security_escalation_err) begin
      `DV_ASSERT_CTRL_REQ("OtpProgH_DataStableWhenBidirectionalAndReq_A", 0)
      `DV_ASSERT_CTRL_REQ("OtpProgReqHighUntilAck_A", 0)
      `DV_ASSERT_CTRL_REQ("OtpProgAckAssertedOnlyWhenReqAsserted_A", 0)
      `DV_ASSERT_CTRL_REQ("KmacIfSyncReqAckAckNeedsReq", 0)
      assertions_disabled = 1;
    end else if (assertions_disabled) begin
      // Reenable assertions if they had been disabled
      `DV_ASSERT_CTRL_REQ("OtpProgH_DataStableWhenBidirectionalAndReq_A", 1)
      `DV_ASSERT_CTRL_REQ("OtpProgReqHighUntilAck_A", 1)
      `DV_ASSERT_CTRL_REQ("OtpProgAckAssertedOnlyWhenReqAsserted_A", 1)
      `DV_ASSERT_CTRL_REQ("KmacIfSyncReqAckAckNeedsReq", 1)
      assertions_disabled = 0;
    end

  endtask


  // smoke test will always return valid next_lc_state
  // need to randomize here because associative array's index cannot be a rand input in constraint
  // verilog_format: off - avoid bad formatting
  virtual function void randomize_next_lc_state(dec_lc_state_e curr_lc_state);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_state,
        // Only lifecycle states
        next_lc_state inside {[DecLcStTestUnlocked0 : DecLcStScrap]};

        if (!err_inj.transition_err && !err_inj.state_err) {
          // Valid transition
          next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]};
        } else if (!err_inj.state_err) {
          // Invalid transition
          !(next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]});
        })
  endfunction
  // verilog_format: on - avoid bad formatting

  virtual function void set_hashed_token();
    lc_ctrl_pkg::token_idx_e token_idx = get_exp_token(dec_lc_state(lc_state), next_lc_state);
    lc_ctrl_pkg::token_idx_e token_idx_err_inj;
    lc_ctrl_state_pkg::lc_token_t tokens_a[NumTokens];
    lc_ctrl_state_pkg::lc_token_t token_err_inj;
    kmac_pkg::rsp_digest_t kmac_digest;

    tokens_a[ZeroTokenIdx]       = lc_ctrl_state_pkg::AllZeroTokenHashed;
    tokens_a[RawUnlockTokenIdx]  = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
    tokens_a[TestUnlockTokenIdx] = cfg.lc_ctrl_vif.otp_i.test_unlock_token;
    tokens_a[TestExitTokenIdx]   = cfg.lc_ctrl_vif.otp_i.test_exit_token;
    tokens_a[RmaTokenIdx]        = cfg.lc_ctrl_vif.otp_i.rma_token;
    tokens_a[InvalidTokenIdx]    = '0;

    if (!err_inj.state_err && !err_inj.count_err && !err_inj.transition_err) begin
      `DV_CHECK_NE(token_idx, InvalidTokenIdx, $sformatf(
                   "curr_state: %0s, next_state %0s, does not expect InvalidToken",
                   lc_state.name,
                   next_lc_state.name
                   ))
    end

    if (!err_inj.token_mismatch_err) begin
      kmac_digest =
          token_to_kmac_digest(tokens_a[token_idx], token_scramble, err_inj.token_invalid_err);
    end else begin
      // Inject token error
      // 50% chance other token data, 50% chance random data
      if ($urandom_range(0, 1)) begin
        // Use other token
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(token_idx_err_inj, token_idx_err_inj != token_idx;)
        kmac_digest = token_to_kmac_digest(tokens_a[token_idx_err_inj], token_scramble);
      end else begin
        // Random token
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(token_err_inj, !(token_err_inj inside {tokens_a});)
        kmac_digest = token_to_kmac_digest(token_err_inj, token_scramble);
      end
    end
    clear_kmac_user_digest_share();
    cfg.m_kmac_app_agent_cfg.add_user_digest_share(kmac_digest);
    // Set error response
    cfg.m_kmac_app_agent_cfg.error_rsp_pct = (err_inj.token_response_err) ? 100 : 0;
  endfunction

  // Set otp program response data
  virtual function void set_otp_prog_rsp();
    bit [1:0] err_bits = 0;
    // Clear any previous data
    cfg.m_otp_prog_pull_agent_cfg.clear_d_user_data();
    // TODO: tailor constraint to LC state transitions for V3
    if (err_inj.otp_prog_err) `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_bits, err_bits == 3;)
    foreach (err_bits[i]) cfg.m_otp_prog_pull_agent_cfg.add_d_user_data(err_bits[i]);
  endfunction

  // Drive OTP input `lc_state` and `lc_cnt`.
  virtual task drive_otp_i(bit rand_otp_i = 1);
    `uvm_info(`gfn, $sformatf("drive_otp_i: started rand_otp_i=%0b err_inj=%p", rand_otp_i, err_inj
              ), UVM_MEDIUM)
    if (rand_otp_i) begin
      if (!err_inj.state_err && !err_inj.state_illegal_err) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_state,
                                           // lc_state should be valid for transition
                                           lc_state inside {LcValidStateForTrans};)
        `uvm_info(`gfn, $sformatf("drive_otp_i: driving lc_state=%s", lc_state.name), UVM_MEDIUM)
      end else begin
        // Force invalid state on input optionally with illegal coding
        lc_state = lc_state_e'(bin_to_lc_state(invalid_lc_state_bin, err_inj.state_illegal_err));
        `uvm_info(`gfn, $sformatf("drive_otp_i: driving invalid state lc_state=%s", lc_state.name),
                  UVM_MEDIUM)
      end

      if (!err_inj.count_err && !err_inj.count_illegal_err) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_cnt,
                                           (lc_state != LcStRaw) -> (lc_cnt != LcCnt0);
        // Count must be less than LcCnt24 unless we want to inject a tranisition count error
        if (!err_inj.transition_count_err) {lc_cnt != LcCnt24;}
        else {lc_cnt == LcCnt24;})
      end else begin
        // Force invalid count on input optionally with illegal coding
        lc_cnt = lc_cnt_e'(bin_to_lc_count(invalid_lc_count_bin, err_inj.count_illegal_err));
        `uvm_info(`gfn, $sformatf(
                  "drive_otp_i: invalid count to otp_i invalid_lc_count_bin='b%b lc_cnt=%h",
                  invalid_lc_count_bin,
                  lc_cnt
                  ), UVM_MEDIUM)
      end

    end else begin
      lc_state = LcStRaw;
      lc_cnt   = LcCnt0;
    end

    cfg.lc_ctrl_vif.init(.lc_state(lc_state), .lc_cnt(lc_cnt),
                         .otp_lc_data_i_valid(!err_inj.otp_lc_data_i_valid_err),
                         .otp_partition_err(err_inj.otp_partition_err),
                         .otp_device_id(cfg.otp_device_id), .otp_manuf_state(cfg.otp_manuf_state),
                         .otp_vendor_test_status(cfg.otp_vendor_test_status));
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state, bit [TL_DW*4-1:0] token_val);
    bit trigger_alert;
    bit terminate_wait_status = 0;
    bit [TL_DW-1:0] status_val = 0;
    uvm_reg_data_t val;

    csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
    while (status_val != CLAIM_TRANS_VAL) begin
      csr_rd(ral.claim_transition_if, status_val);
    end

    csr_wr(ral.transition_target, {DecLcStateNumRep{next_lc_state[DecLcStateWidth-1:0]}});
    foreach (ral.transition_token[i]) begin
      csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
      token_val = token_val >> TL_DW;
    end

    // Write OTP vendor test reg
    csr_wr(ral.otp_vendor_test_ctrl, cfg.otp_vendor_test_ctrl);
    // Check  OTP vendor test status
    if (!err_inj.lc_fsm_backdoor_err && !err_inj.kmac_fsm_backdoor_err &&
        !err_inj.count_backdoor_err && !err_inj.state_backdoor_err) begin
      // Don't check for backdoor error injection as the results
      // are unpredictable
      csr_rd(ral.otp_vendor_test_status, val);
    end

    fork
      begin : transition_process
        csr_wr(ral.transition_cmd, 'h01);
        // Wait for status done or terminal errors
        `DV_SPINWAIT(wait_status(trigger_alert, terminate_wait_status);)
        // always on alert, set time delay to make sure alert triggered
        // for at least for one  handshake cycle
        if (trigger_alert) cfg.clk_rst_vif.wait_clks($urandom_range(50, 20));
      end
      begin : inject_escalate_process
        if (err_inj.security_escalation_err) begin
          security_escalation_inject();
          cfg.clk_rst_vif.wait_clks($urandom_range(50, 100));
          // Do not bother waiting for completion status
          terminate_wait_status = 1;
        end
      end
    join


  endtask

  // Wait for status done or terminal errors
  virtual task wait_status(ref bit expect_alert, ref bit terminate);
    bit [TL_DW-1:0] status_val;
    bit state_error_exp, state_error_act;
    bit count_error_exp, count_error_act;
    bit token_error_exp, token_error_act;
    bit flash_rma_error_exp, flash_rma_error_act;
    bit otp_error_exp, otp_error_act;
    bit transition_count_error_exp, transition_count_error_act;
    bit otp_partition_error_exp, otp_partition_error_act;

    // verilog_format: off - avoid bad formatting
    forever begin
      // If we are in random escalate injection state delay a little to
      // allow the escalate to be recognised
      if (cfg.test_phase == LcCtrlRandomEscalate) cfg.clk_rst_vif.wait_clks(5);
      csr_rd(ral.status, status_val);
      `uvm_info(`gfn, {"wait_status: ", ral.status.sprint(uvm_default_line_printer)}, UVM_MEDIUM)
      if (get_field_val(ral.status.transition_successful, status_val)) break;
      if (get_field_val(ral.status.token_error, status_val)) break;
      if (get_field_val(ral.status.flash_rma_error, status_val)) break;
      if (get_field_val(ral.status.transition_error, status_val)) break;
      if (get_field_val(ral.status.transition_count_error, status_val)) break;
      // if (get_field_val(ral.status.otp_partition_error, status_val)) break;
      if (get_field_val(ral.status.otp_error, status_val) ||
          get_field_val(ral.status.state_error, status_val) ||
          get_field_val(ral.status.bus_integ_error, status_val)) begin
        expect_alert = 1;
        break;
      end
      // verilog_format: on
      // Random delay to next read
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 3));

      // Allow us to quit from waiting in a quiescent state
      if (terminate) break;
    end

    // Expected bits
    state_error_exp = cfg.err_inj.state_err || cfg.err_inj.count_err ||
        cfg.err_inj.state_illegal_err || cfg.err_inj.count_illegal_err ||
        cfg.err_inj.lc_fsm_backdoor_err || cfg.err_inj.kmac_fsm_backdoor_err ||
        cfg.err_inj.count_backdoor_err || cfg.err_inj.state_backdoor_err;
    token_error_exp = cfg.err_inj.token_mismatch_err || cfg.err_inj.token_response_err ||
        cfg.err_inj.token_invalid_err;
    flash_rma_error_exp = cfg.err_inj.flash_rma_error_rsp;
    otp_error_exp = cfg.err_inj.otp_prog_err || cfg.err_inj.clk_byp_error_rsp;
    transition_count_error_exp = cfg.err_inj.transition_count_err;
    otp_partition_error_exp = cfg.err_inj.otp_partition_err;

    // Actual bits
    state_error_act = get_field_val(ral.status.state_error, status_val);
    token_error_act = get_field_val(ral.status.token_error, status_val);
    flash_rma_error_act = get_field_val(ral.status.flash_rma_error, status_val);
    otp_error_act = get_field_val(ral.status.otp_error, status_val);
    transition_count_error_act = get_field_val(ral.status.transition_count_error, status_val);
    otp_partition_error_act = get_field_val(ral.status.otp_partition_error, status_val);

    if (!terminate) begin
      // Check status against expected from err_inj
      `DV_CHECK_EQ(state_error_act, state_error_exp)
      `DV_CHECK_EQ(token_error_act, token_error_exp)
      `DV_CHECK_EQ(flash_rma_error_act, flash_rma_error_exp)
      `DV_CHECK_EQ(otp_error_act, otp_error_exp)
      `DV_CHECK_EQ(transition_count_error_exp, transition_count_error_act)
      `DV_CHECK_EQ(otp_partition_error_exp, otp_partition_error_act)
    end

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
    // Debug signal in lc_ctrl_if
    cfg.lc_ctrl_vif.err_inj <= err_inj;
    `uvm_info(`gfn, $sformatf("update_err_inj_cfg: %p", cfg.err_inj), UVM_MEDIUM)
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

  // Flip bits in LC FSM registers
  protected virtual task lc_fsm_backdoor_err_inj();
    logic [FsmStateWidth-1:0] state;
    state = cfg.lc_ctrl_vif.lc_fsm_state_backdoor_read();
    state ^= lc_fsm_state_invert_bits;
    cfg.lc_ctrl_vif.lc_fsm_state_backdoor_write(state, 0, lc_fsm_state_err_inj_period);
  endtask

  // Flip bits in KMAC FSM registers
  protected virtual task kmac_fsm_backdoor_err_inj();
    logic [KMAC_FSM_WIDTH-1:0] state;
    state = cfg.lc_ctrl_vif.kmac_fsm_state_backdoor_read();
    state ^= kmac_fsm_state_invert_bits;
    cfg.lc_ctrl_vif.kmac_fsm_state_backdoor_write(state, 0, lc_fsm_state_err_inj_period);
  endtask


  // Flip bits in OTP State input
  protected virtual task state_backdoor_err_inj();
    logic [LcStateWidth-1:0] state;
    state = cfg.lc_ctrl_vif.count_backdoor_read();
    state ^= state_invert_bits;
    cfg.lc_ctrl_vif.count_backdoor_write(state, 0, state_err_inj_period);
  endtask

  // Flip bits OTP Count input
  protected virtual task count_backdoor_err_inj();
    logic [LcCountWidth-1:0] count;
    count = cfg.lc_ctrl_vif.count_backdoor_read();
    count ^= count_invert_bits;
    cfg.lc_ctrl_vif.count_backdoor_write(count, 0, count_err_inj_period);
  endtask

  // Send an escalate alert
  // Deassert after an number of clock cycles if assert clocks > 0
  // Otherwise leave asserted
  protected virtual task send_escalate(int index, int assert_clocks = 0);
    // TODO - replace with calls to escalate agent when driver implemented
    unique case (index)
      0: begin
        cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
        if (assert_clocks > 0) begin
          cfg.clk_rst_vif.wait_clks(assert_clocks);
          cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
        end
      end
      1: begin
        cfg.m_esc_scrap_state1_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
        if (assert_clocks > 0) begin
          cfg.clk_rst_vif.wait_clks(assert_clocks);
          cfg.m_esc_scrap_state1_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
        end
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Invalid index %0d", index))
      end
    endcase
  endtask

  // Clear escalate assertion
  protected virtual task clear_escalate(int index);
    // TODO - replace with calls to escalate agent when driver implemented
    unique case (index)
      0: begin
        cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
      end
      1: begin
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
  protected virtual task handle_fatal_prog_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_prog_error: alert received"), UVM_MEDIUM)
    fatal_prog_alert_received = 1;
  endtask

  protected virtual task handle_fatal_state_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_state_error: alert received"), UVM_MEDIUM)
    fatal_state_alert_received = 1;
  endtask

  protected virtual task handle_fatal_bus_integ_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_bus_integ_error: alert received"), UVM_MEDIUM)
    fatal_bus_integ_alert_received = 1;
  endtask

  // Assert escalate at the appropriate part of the test
  protected virtual task handle_escalate();
    forever begin
      @(cfg.set_test_phase_ev);
      if (cfg.get_test_phase() == LcCtrlEscalate) begin
        if( fatal_prog_alert_received ||
            fatal_state_alert_received || fatal_bus_integ_alert_received ) begin
          send_escalate($urandom_range(1, 0), 100);
        end
      end
    end
  endtask

  // verilog_format: off
  virtual task run_clk_byp_rsp_nonblocking(bit has_err = 0);
    fork
      forever begin
        lc_ctrl_pkg::lc_tx_t rsp = lc_ctrl_pkg::Off;
        wait (cfg.lc_ctrl_vif.clk_byp_req_o == lc_ctrl_pkg::On || err_inj.clk_byp_error_rsp);
        if (err_inj.clk_byp_error_rsp) begin
          // Error stream just on -> off -> on... every clock cycle
          rsp = (rsp == lc_ctrl_pkg::On) ? lc_ctrl_pkg::Off : lc_ctrl_pkg::On;
          cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
          cfg.clk_rst_vif.wait_clks(1);
        end else begin
          // Normal behaviour
          rsp = lc_ctrl_pkg::On;
          cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
          cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
        end
        wait (cfg.lc_ctrl_vif.clk_byp_req_o != lc_ctrl_pkg::On || err_inj.clk_byp_error_rsp);
        if (err_inj.clk_byp_error_rsp) begin
          // Error stream just on -> off -> on... every clock cycle
          rsp = (rsp == lc_ctrl_pkg::On) ? lc_ctrl_pkg::Off : lc_ctrl_pkg::On;
          cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
          cfg.clk_rst_vif.wait_clks(1);
        end else begin
          // Normal behaviour
          rsp = lc_ctrl_pkg::Off;
          cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
          cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
        end
      end
    join_none
  endtask


  virtual task run_flash_rma_rsp_nonblocking(bit has_err = 0);
    fork
      forever begin
        lc_ctrl_pkg::lc_tx_t rsp = lc_ctrl_pkg::Off;
        wait (cfg.lc_ctrl_vif.flash_rma_req_o == lc_ctrl_pkg::On || err_inj.flash_rma_error_rsp);
        if (err_inj.flash_rma_error_rsp) begin
          // Error stream just on -> off -> on... every clock cycle
          rsp = (rsp == lc_ctrl_pkg::On) ? lc_ctrl_pkg::Off : lc_ctrl_pkg::On;
          cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
          cfg.clk_rst_vif.wait_clks(1);
        end else begin
          // Normal behaviour
          rsp = lc_ctrl_pkg::On;
          cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
          cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
        end
        wait (cfg.lc_ctrl_vif.flash_rma_req_o != lc_ctrl_pkg::On || err_inj.flash_rma_error_rsp);
        if (err_inj.flash_rma_error_rsp) begin
          // Error stream just on -> off -> on... every clock cycle
          rsp = (rsp == lc_ctrl_pkg::On) ? lc_ctrl_pkg::Off : lc_ctrl_pkg::On;
          cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
          cfg.clk_rst_vif.wait_clks(1);
        end else begin
          // Normal behaviour
          rsp = lc_ctrl_pkg::Off;
          cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
          cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
        end
      end
    join_none
  endtask
  // verilog_format: on

  // Security escalation injection task
  virtual task security_escalation_inject();
    cfg.clk_rst_vif.wait_clks(security_escalation_err_inj_delay);
    cfg.set_test_phase(LcCtrlRandomEscalate);
    fork
      if (security_escalation_err_inj_channels[0]) send_escalate(0);
      if (security_escalation_err_inj_channels[1]) send_escalate(1);
    join
  endtask

endclass
