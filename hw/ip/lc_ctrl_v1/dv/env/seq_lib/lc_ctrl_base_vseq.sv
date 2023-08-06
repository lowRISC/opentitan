// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (lc_ctrl_reg_block),
  .CFG_T              (lc_ctrl_env_cfg),
  .COV_T              (lc_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(lc_ctrl_virtual_sequencer)
);
  `uvm_object_utils(lc_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_lc_ctrl_init = 1'b1;

  lc_ctrl_state_pkg::lc_state_e lc_state;
  lc_ctrl_state_pkg::lc_cnt_e lc_cnt;

  `uvm_object_new

  // In jtag_riscv_agent_cfg, setting the in_reset value to 1 will trigger the dmi_agent to reset.
  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
      super.apply_reset(kind);
      cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
    end
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.escalate_injected = 0;
    cfg.otp_vendor_test_status = 0;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    super.apply_resets_concurrently(reset_duration_ps);
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  virtual task pre_start();
    // LC_CTRL does not have interrupts
    do_clear_all_interrupts = 0;
    // Set the sequence typename in the interface to aid debugging
    cfg.lc_ctrl_vif.set_test_sequence_typename(this.get_type_name());
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // Clear static signals so we get transitions for toggle coverage
    cfg.lc_ctrl_vif.clear_static_signals();
    // OTP inputs `lc_state` and `lc_cnt` need to be stable before lc_ctrl's reset is deasserted
    if (do_lc_ctrl_init) begin
      drive_otp_i();
      cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
    end
    super.dut_init();
    if (do_lc_ctrl_init) lc_ctrl_init();
  endtask

  // Drive OTP input `lc_state` and `lc_cnt`.
  virtual task drive_otp_i(bit rand_otp_i = 1);
    if (rand_otp_i) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(lc_state)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lc_cnt, (lc_state != LcStRaw) -> (lc_cnt != LcCnt0);)
    end else begin
      lc_state = LcStRaw;
      lc_cnt   = LcCnt0;
    end

    cfg.lc_ctrl_vif.init(.lc_state(lc_state), .lc_cnt(lc_cnt), .otp_device_id(cfg.otp_device_id),
                         .otp_manuf_state(cfg.otp_manuf_state),
                         .otp_vendor_test_status(cfg.otp_vendor_test_status));

  endtask

  // Read OTP CSRs
  virtual task read_otp_csrs();
    uvm_reg_data_t val;
    foreach (ral.device_id[i]) csr_rd(ral.device_id[i], val);
    foreach (ral.manuf_state[i]) csr_rd(ral.manuf_state[i], val);
    // Hardware revision reg
    csr_rd(ral.hw_revision0, val);
    csr_rd(ral.hw_revision1, val);
  endtask


  // Drive LC init pin.
  virtual task lc_ctrl_init();
    cfg.set_test_phase(LcCtrlLcInit);
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 1);
    // Dont wait for response from DUT if we are holding otp_lc_data_i.valid low
    if (!cfg.err_inj.otp_lc_data_i_valid_err) begin
      `DV_SPINWAIT(wait(cfg.pwr_lc_vif.pins[LcPwrDoneRsp] == 1);)
    end else begin
      cfg.clk_rst_vif.wait_clks($urandom_range(3, 10));
    end
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
  endtask

  // some registers won't set to default value until otp_init is done
  virtual task read_and_check_all_csrs_after_reset();
    lc_ctrl_init();
    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task run_clk_byp_rsp(bit has_err = 0);
    forever begin
      lc_ctrl_pkg::lc_tx_t rsp;
      wait(cfg.lc_ctrl_vif.clk_byp_req_o == lc_ctrl_pkg::On);
      rsp = (has_err) ? ($urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off) :
          lc_ctrl_pkg::On;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
      cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);

      wait(cfg.lc_ctrl_vif.clk_byp_req_o != lc_ctrl_pkg::On);
      rsp = (has_err) ? ($urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off) :
          lc_ctrl_pkg::Off;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
      cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
    end
  endtask

  virtual task run_flash_rma_rsp(bit has_err = 0);
    forever begin
      lc_ctrl_pkg::lc_tx_t rsp;
      wait(cfg.lc_ctrl_vif.flash_rma_req_o == lc_ctrl_pkg::On);
      rsp = (has_err) ? ($urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off) :
          lc_ctrl_pkg::On;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
      cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);

      wait(cfg.lc_ctrl_vif.flash_rma_req_o != lc_ctrl_pkg::On);
      rsp = (has_err) ? ($urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off) :
          lc_ctrl_pkg::Off;
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
      cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
    end
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state, bit [TL_DW*4-1:0] token_val);
    bit trigger_alert;
    bit [TL_DW-1:0] status_val;
    uvm_reg_data_t val;
    csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
    if ($urandom_range(0, 1)) csr_wr(ral.transition_ctrl, $urandom_range(0, 1));
    csr_wr(ral.transition_target, {DecLcStateNumRep{next_lc_state[DecLcStateWidth-1:0]}});
    foreach (ral.transition_token[i]) begin
      csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
      token_val = token_val >> TL_DW;
    end
    // Write vendor test reg
    csr_wr(ral.otp_vendor_test_ctrl, cfg.otp_vendor_test_ctrl);
    // Check  OTP vendor test status
    csr_rd(ral.otp_vendor_test_status, val);

    // Execute transition
    csr_wr(ral.transition_cmd, 'h01);

    // Wait for status done or terminal errors
    `DV_SPINWAIT(while (1) begin
          csr_rd(ral.status, status_val);
          if (get_field_val(ral.status.transition_successful, status_val)) break;
          if (get_field_val(ral.status.token_error, status_val)) break;
          if (get_field_val(ral.status.otp_error, status_val)) begin
            trigger_alert = 1;
            break;
          end
        end)

    // always on alert, set time delay to make sure alert triggered for at least for one
    // handshake cycle
    if (trigger_alert) cfg.clk_rst_vif.wait_clks($urandom_range(20, 50));
  endtask

  // checking of these two CSRs are done in scb
  virtual task rd_lc_state_and_cnt_csrs();
    bit [TL_DW-1:0] val;
    csr_rd(ral.lc_state, val);
    csr_rd(ral.lc_transition_cnt, val);
  endtask

  // Sample the coverage for this sequence
  virtual function void sample_cov();
    // Only if coverage enabled
    if (cfg.en_cov) begin
      p_sequencer.cov.sample_cov();
    end
  endfunction

  // Create a string with "called from (filename:line number)" to be used in csr checks etc.
  virtual function string called_from(string filename, int lineno);
    return $sformatf("called from %s: %0d", filename, lineno);
  endfunction

  // Create a kmac digest from a token
  virtual function kmac_pkg::rsp_digest_t token_to_kmac_digest(
      lc_token_t token, lc_token_t scramble, bit err_inj = 0);
    kmac_pkg::rsp_digest_t digest;
    lc_token_t bit_flip;

    // Randomize upper bits of digest
    `DV_CHECK_STD_RANDOMIZE_FATAL(digest);

    // Set the significant bits of the digest
    digest.digest_share0[LcTokenWidth-1:0] = token ^ scramble;
    digest.digest_share1[LcTokenWidth-1:0] = scramble;

    if (err_inj) begin
      // Inject an error by flipping a bit in one of the entries
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bit_flip, $onehot(bit_flip);)
      if ($urandom_range(0, 1)) digest.digest_share0 ^= bit_flip;
      else digest.digest_share1 ^= bit_flip;
    end
    return digest;
  endfunction

  // Clear kmac agent digest data
  virtual function void clear_kmac_user_digest_share();
    while (cfg.m_kmac_app_agent_cfg.has_user_digest_share()) begin
      void'(cfg.m_kmac_app_agent_cfg.get_user_digest_share());
    end
  endfunction

  // Does this transition require a test unlock or test exit token
  virtual function bit has_test_token(input dec_lc_state_e dec_lc_state,
                                      input dec_lc_state_e next_lc_state);
    has_test_token = (TransTokenIdxMatrix[dec_lc_state][next_lc_state] inside {
        TestUnlockTokenIdx, TestExitTokenIdx});
    `uvm_info(`gfn, $sformatf(
              "has_test_token: checking state %s -> %s result %0b",
              dec_lc_state.name(),
              next_lc_state.name(),
              has_test_token
              ), UVM_MEDIUM)
  endfunction

  // Does this transition require an RMA token
  virtual function bit has_rma_token(input dec_lc_state_e dec_lc_state,
                                     input dec_lc_state_e next_lc_state);
    has_rma_token = (TransTokenIdxMatrix[dec_lc_state][next_lc_state] inside {RmaTokenIdx});
    `uvm_info(`gfn, $sformatf(
              "has_rma_token: checking state %s -> %s result %0b",
              dec_lc_state.name(),
              next_lc_state.name(),
              has_rma_token
              ), UVM_MEDIUM)
  endfunction

endclass : lc_ctrl_base_vseq
