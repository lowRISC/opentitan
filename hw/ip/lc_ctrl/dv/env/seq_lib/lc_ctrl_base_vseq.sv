// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (lc_ctrl_reg_block),
  .CFG_T              (lc_ctrl_env_cfg),
  .COV_T              (lc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(lc_ctrl_virtual_sequencer)
);

  // Process to handle alerts
  protected process handle_alerts_process;

  // various knobs to enable certain routines
  bit do_lc_ctrl_init = 1'b1;

  lc_ctrl_state_pkg::lc_state_e lc_state;
  lc_ctrl_state_pkg::lc_cnt_e lc_cnt;

  dec_lc_state_e next_lc_state;

  // Error injection control
  rand lc_ctrl_err_inj_t err_inj;

  // Invalid lc_state lc_count as a binary representation
  rand lc_state_bin_t invalid_lc_state_bin;
  rand lc_count_bin_t invalid_lc_count_bin;
  rand bit [DecLcStateWidth-1:0] invalid_next_state;
  rand bit [15:0] fsm_state_invert_bits;
  rand int unsigned fsm_state_err_inj_delay;
  rand int unsigned fsm_state_err_inj_period;

  `uvm_object_utils_begin(lc_ctrl_base_vseq)
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

  constraint lc_state_err_c {
    err_inj.state_err          == 0;
    err_inj.state_backdoor_err == 0;
    err_inj.count_err          == 0;
    err_inj.count_backdoor_err == 0;
    err_inj.transition_err     == 0;
  }

  constraint invalid_states_bin_c {
    !(invalid_lc_state_bin inside {ValidLcStatesBin});
    !(invalid_lc_count_bin inside {ValidLcCountsBin});
    !(invalid_next_state inside {ValidDecodedStates});
  }

  constraint fsm_state_invert_bits_c {
    // Just one bit flipped by default
    $onehot(fsm_state_invert_bits);
  }

  constraint fsm_state_err_inj_delay_c {
    fsm_state_err_inj_delay inside {[1 : 200]};
    fsm_state_err_inj_period inside {[2 : 4]};
  }

  virtual task pre_start();
    // LC_CTRL does not have interrupts
    do_clear_all_interrupts = 0;
    // Spawn alert handler
    fork
      handle_alerts();
    join_none

    super.pre_start();
  endtask

  virtual task post_start();
    // Kill alert handler
    if (handle_alerts_process != null) handle_alerts_process.kill;
    super.post_start();
  endtask


  virtual task dut_init(string reset_kind = "HARD");
    // OTP inputs `lc_state` and `lc_cnt` need to be stable before lc_ctrl's reset is deasserted
    if (do_lc_ctrl_init) begin
      drive_otp_i();
      cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
    end
    super.dut_init();
    if (do_lc_ctrl_init) lc_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending lc_ctrl operations and wait for them to complete
    // TODO
  endtask

  // Drive OTP input `lc_state` and `lc_cnt`.
  virtual task drive_otp_i(bit rand_otp_i = 1);
    if (rand_otp_i) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(lc_state)
      if (err_inj.state_err) begin
        // Force invalid state on input
        lc_state = bin_to_lc_state(invalid_lc_state_bin);
      end
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_cnt, (lc_state != LcStRaw) -> (lc_cnt != LcCnt0);)
    end else begin
      lc_state = LcStRaw;
      lc_cnt   = LcCnt0;
    end
    cfg.lc_ctrl_vif.init(lc_state, lc_cnt);
  endtask

  // Drive LC init pin.
  virtual task lc_ctrl_init();
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 1);
    wait(cfg.pwr_lc_vif.pins[LcPwrDoneRsp] == 1);
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
  endtask

  // some registers won't set to default value until otp_init is done
  virtual task read_and_check_all_csrs_after_reset();
    lc_ctrl_init();
    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task run_clk_byp_rsp_nonblocking(bit has_err = 0);
    fork
      forever begin
        lc_ctrl_pkg::lc_tx_t rsp;
        wait(cfg.lc_ctrl_vif.clk_byp_req_o == lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
            lc_ctrl_pkg::On;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);

        wait(cfg.lc_ctrl_vif.clk_byp_req_o != lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
            lc_ctrl_pkg::Off;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
      end
    join_none
  endtask

  virtual task run_flash_rma_rsp_nonblocking(bit has_err = 0);
    fork
      forever begin
        lc_ctrl_pkg::lc_tx_t rsp;
        wait(cfg.lc_ctrl_vif.flash_rma_req_o == lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
            lc_ctrl_pkg::On;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);

        wait(cfg.lc_ctrl_vif.flash_rma_req_o != lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
            lc_ctrl_pkg::Off;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
      end
    join_none
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

    // Wait for status done or terminal errors
    `DV_SPINWAIT(wait_status(trigger_alert);)

    // always on alert, set time delay to make sure alert triggered for at least for one
    // handshake cycle
    if (trigger_alert) cfg.clk_rst_vif.wait_clks($urandom_range(50, 20));
  endtask

  // Wait for status done or terminal errors
  virtual task wait_status(ref bit expect_alert);
    bit [TL_DW-1:0] status_val;
    forever begin
      csr_rd(ral.status, status_val);
      `uvm_info(`gfn, {"wait_status: ", ral.status.sprint(uvm_default_line_printer)}, UVM_MEDIUM)
      if (get_field_val(ral.status.transition_successful, status_val)) break;
      if (get_field_val(ral.status.token_error, status_val)) break;
      if (get_field_val(ral.status.otp_error, status_val) ||
          get_field_val(ral.status.state_error, status_val) ||
          get_field_val(ral.status.bus_integ_error, status_val)
          ) begin
        expect_alert = 1;
        break;
      end
      // Random delay to next read
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 1));
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
    `uvm_info(`gfn, $sformatf("update_err_inj_cfg: %p", cfg.err_inj),
              UVM_MEDIUM)
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

  // Individual event handlers
  protected virtual task handle_fatal_prog_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_prog_error: alert received"), UVM_MEDIUM)
  endtask

  protected virtual task handle_fatal_state_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_state_error: alert received"), UVM_MEDIUM)
  endtask

  protected virtual task handle_fatal_bus_integ_error;
    `uvm_info(`gfn, $sformatf("handle_fatal_bus_integ_error: alert received"), UVM_MEDIUM)
  endtask

  // Flip bits in FSM
  protected virtual task fsm_backdoor_err_inj();
    logic [15:0] fsm_state;
    fsm_state = cfg.lc_ctrl_vif.fsm_state_backdoor_read();
    fsm_state ^= fsm_state_invert_bits;
    cfg.lc_ctrl_vif.fsm_state_backdoor_write(fsm_state, 0, fsm_state_err_inj_period);
  endtask

  // Send an escalate alert
  protected virtual task send_escalate(int index);
    // TODO - replace with calls to escalate agent when driver implemented
    unique case (index)
      0: begin
        cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
        #10us;
        cfg.m_esc_scrap_state0_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
      end
      1: begin
        cfg.m_esc_scrap_state1_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
        #10us;
        cfg.m_esc_scrap_state1_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
      end
    endcase
  endtask

  // do_print - do a better job of printing structures etc.
  virtual function void do_print(uvm_printer printer);
    super.do_print(printer);
    // err_inj
    printer.print_generic(
   	    .name("err_inj"),
   	    .type_name("lc_ctrl_err_inj_t"),
   	    .size($bits(err_inj)),
   	    .value($sformatf("%p", err_inj))
        );

  endfunction

endclass : lc_ctrl_base_vseq
