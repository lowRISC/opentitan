// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test triggers otp_macro error by forcing an invalid cmd_i into prim_generic_otp.
class otp_ctrl_macro_invalid_cmd_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_macro_invalid_cmd_vseq)

  `uvm_object_new

  rand otp_ctrl_part_pkg::part_idx_e exp_macro_err;

  bit [NumPart+1:0] act_macro_err;
  bit               exp_buffer_err;

  // This variable is declared for DAI err_code functional coverage.
  // Default to DaiIdx that won't be sampled in dai_err_code.
  // Only update this value if the err_code is DaiIdx.
  int dai_macro_err_part_idx = DaiIdx;

  constraint macro_err_c {exp_macro_err inside {[CreatorSwCfgIdx:LciIdx]};}

  virtual task pre_start();
    super.pre_start();
    exp_macro_err.rand_mode(0);
  endtask

 task body();
    otp_err_code_e    err_code;
    dv_base_reg_field err_code_flds[$];
    ral.err_code.get_dv_base_reg_fields(err_code_flds);
    is_valid_dai_op = 0;
    exp_buffer_err  = exp_macro_err inside {[HwCfgIdx : LifeCycleIdx]};

    for (uint i = 0; i <= num_dai_op; i++) begin
      bit [TL_DW-1:0] tlul_val;

      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting dai access seq %0d/%0d with addr %0h in partition %0d",
                i, num_dai_op, dai_addr, part_idx), UVM_MEDIUM)

        if (act_macro_err == 0 && ($urandom_range(0, 1) || i == num_dai_op)) begin
          `uvm_info(`gfn, $sformatf("Force otp macro error with part %0d", exp_macro_err), UVM_LOW)
          force_macro_error();
          case (exp_macro_err)
            CreatorSwCfgIdx, OwnerSwCfgIdx: begin
              bit [TL_DW-1:0] sw_dai_addr;
              uvm_reg_addr_t tlul_addr;
              sw_dai_addr = (exp_macro_err == CreatorSwCfgIdx) ?
                            $urandom_range(CreatorSwCfgOffset, CreatorSwCfgDigestOffset) :
                            $urandom_range(OwnerSwCfgOffset, OwnerSwCfgDigestOffset);
              tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(sw_dai_addr));
              tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1), .check_rsp(0));
            end
            HwCfgIdx, Secret0Idx, Secret1Idx, Secret2Idx, LifeCycleIdx: begin
              trigger_checks('1);
            end
            LciIdx: begin
              req_lc_transition(.check_intr(0), .blocking(0));
              // Max delay for push-pull agent to send a request
              cfg.clk_rst_vif.wait_clks(1000);
            end
            DaiIdx: begin
              dai_rd(dai_addr, 0, wdata0, wdata1);
              dai_macro_err_part_idx = get_part_index(dai_addr);
            end
            default: `uvm_fatal(`gfn, $sformatf("exp_macro_err %0h not supported", exp_macro_err))
          endcase
          act_macro_err[exp_macro_err] = 1;
          check_and_release_macro_error();
        end

      dai_wr(dai_addr, wdata0, wdata1);

      // OTP read via DAI, check data in scb
      dai_rd(dai_addr, 0, wdata0, wdata1);

      // If write sw partitions, check tlul window
      if (is_sw_part(dai_addr)) begin
        uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
        tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1), .check_rsp(0));
      end

      csr_rd(ral.status, tlul_val);
    end

    foreach (act_macro_err[i]) begin
      if (act_macro_err[i]) begin
        csr_rd_check(.ptr(err_code_flds[i]), .compare_value(OtpMacroError));
        if (cfg.en_cov) cov.collect_err_code_field_cov(i, OtpMacroError, dai_macro_err_part_idx);
      end
    end

    // Issue reset to stop fatal alert
    apply_reset();
    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
  endtask

  virtual task force_macro_error();
    if (exp_buffer_err) cfg.otp_ctrl_vif.force_invalid_part_cmd_o(exp_macro_err);
    else                cfg.otp_ctrl_vif.force_invalid_otp_cmd_i();
    cfg.en_scb = 0;
    cfg.en_scb_tl_err_chk = 0;
  endtask

  virtual task check_and_release_macro_error();
    string alert_name = "fatal_macro_error";
    int max_wait_cycles = (cfg.m_alert_agent_cfg[alert_name].ack_delay_max +
                           cfg.m_alert_agent_cfg[alert_name].ack_stable_max) *
                          ($ceil(cfg.clk_rst_vif.clk_freq_mhz /
                           cfg.m_alert_agent_cfg[alert_name].vif.clk_rst_async_if.clk_freq_mhz));

    `DV_SPINWAIT_EXIT(wait(cfg.m_alert_agent_cfg[alert_name].vif.alert_tx_final.alert_p);,
        cfg.clk_rst_vif.wait_clks(max_wait_cycles);,
        $sformatf("Timeout waiting for alert %0s", alert_name))
    check_fatal_alert_nonblocking(alert_name);

    if (exp_buffer_err) cfg.otp_ctrl_vif.release_invalid_part_cmd_o(exp_macro_err);
    else                cfg.otp_ctrl_vif.release_invalid_otp_cmd_i();
  endtask

endclass
