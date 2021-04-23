// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface collect the broadcast output data from OTP,
// and drive input requests coming into OTP.
`define ECC_REG_PATH u_otp_ctrl_ecc_reg.gen_ecc_dec[0].u_prim_secded_72_64_dec

interface otp_ctrl_if(input clk_i, input rst_ni);
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;

  // output from DUT
  otp_hw_cfg_t         otp_hw_cfg_o;
  otp_keymgr_key_t     keymgr_key_o;
  otp_lc_data_t        lc_data_o;
  logic                pwr_otp_done_o, pwr_otp_idle_o;

  // inputs to DUT
  logic                pwr_otp_init_i;
  lc_ctrl_pkg::lc_tx_e lc_dft_en_i, lc_escalate_en_i, lc_check_byp_en_i,
                       lc_creator_seed_sw_rw_en_i, lc_seed_hw_rd_en_i;
  otp_ast_rsp_t        otp_ast_pwr_seq_h_i;

  // probe design signal for alert request
  logic                alert_reqs;

  // connect with lc_prog push-pull interface
  logic                lc_prog_req, lc_prog_err;
  logic                lc_prog_err_dly1, lc_prog_no_sta_check;

  // LC_escalate_en is async, take two clock cycles to sync.
  lc_ctrl_pkg::lc_tx_e lc_esc_dly1, lc_esc_dly2;
  // For lc_escalate_en, every value that is not Off is a On.
  bit                  lc_esc_on;
  // Usually the lc_check_byp will be automatically set to On when lc_prog_req is issued but reset
  // has not been issued, otherwise internal check will fail.
  // Set this variable to 0 might cause otp_check_fail.
  bit                  lc_check_byp_en = 1;
  bit [1:0]            force_sw_parts_ecc_reg;

  // Lc_err could trigger during LC program, so check intr and status after lc_req is finished.
  // Lc_err takes one clock cycle to propogate to intr signal. So avoid intr check if it happens
  // during the transition.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lc_prog_err_dly1  <= 0;
      lc_esc_dly1       <= lc_ctrl_pkg::Off;
      lc_esc_dly2       <= lc_ctrl_pkg::Off;
      lc_check_byp_en_i <= lc_ctrl_pkg::Off;
      lc_esc_on         <= 0;
    end else begin
      lc_prog_err_dly1 <= lc_prog_err;
      lc_esc_dly1      <= lc_escalate_en_i;
      lc_esc_dly2      <= lc_esc_dly1;
      if (lc_prog_req && lc_check_byp_en_i == lc_ctrl_pkg::Off && lc_check_byp_en) begin
        lc_check_byp_en_i <= lc_ctrl_pkg::On;
      end
      if (lc_esc_dly2 == lc_ctrl_pkg::On && !lc_esc_on) begin
        lc_esc_on <= 1;
      end
    end
  end

  assign lc_prog_no_sta_check = lc_prog_err | lc_prog_err_dly1 | lc_prog_req | lc_esc_on;

  // TODO: for lc_tx, except esc_en signal, all value different from On is treated as Off,
  // technically we can randomize values here once scb supports
  task automatic init(lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en_val = lc_ctrl_pkg::On);
    lc_creator_seed_sw_rw_en_i = lc_ctrl_pkg::On;
    lc_seed_hw_rd_en_i         = lc_seed_hw_rd_en_val;
    lc_dft_en_i                = lc_ctrl_pkg::Off;
    lc_escalate_en_i           = lc_ctrl_pkg::Off;
    lc_check_byp_en_i          = lc_ctrl_pkg::Off;
    pwr_otp_init_i             = 0;
    // ast_pwr_seq is dummy in open sourced OTP memory
    otp_ast_pwr_seq_h_i        = $urandom();
  endtask

  task automatic drive_pwr_otp_init(logic val);
    pwr_otp_init_i = val;
  endtask

  task automatic drive_lc_creator_seed_sw_rw_en_i(lc_ctrl_pkg::lc_tx_e val);
    lc_creator_seed_sw_rw_en_i = val;
  endtask

  task automatic drive_lc_dft_en(lc_ctrl_pkg::lc_tx_e val);
    lc_dft_en_i = val;
  endtask

  task automatic drive_lc_escalate_en(lc_ctrl_pkg::lc_tx_e val);
    lc_escalate_en_i = val;
  endtask

  function automatic bit under_error_states();
    return lc_esc_on | alert_reqs;
  endfunction

  // SW partitions do not have any internal checks.
  // Here we force internal ECC check to fail.
  task automatic force_sw_check_fail(bit[1:0] fail_idx = $urandom_range(1, 3));
    @(posedge clk_i);
    if (fail_idx[0]) begin
      force tb.dut.gen_partitions[0].gen_unbuffered.u_part_unbuf.`ECC_REG_PATH.syndrome_o[0] = 1;
      force_sw_parts_ecc_reg[0] = 1;
    end
    if (fail_idx[1]) begin
      force tb.dut.gen_partitions[1].gen_unbuffered.u_part_unbuf.`ECC_REG_PATH.syndrome_o[0] = 1;
      force_sw_parts_ecc_reg[1] = 1;
    end
  endtask

  task automatic release_sw_check_fail(bit[1:0] fail_idx);
    @(posedge clk_i);
    if (fail_idx[0]) begin
      release tb.dut.gen_partitions[0].gen_unbuffered.u_part_unbuf.`ECC_REG_PATH.syndrome_o[0];
      force_sw_parts_ecc_reg[0] = 0;
    end
    if (fail_idx[1]) begin
      release tb.dut.gen_partitions[1].gen_unbuffered.u_part_unbuf.`ECC_REG_PATH.syndrome_o[0];
      force_sw_parts_ecc_reg[0] = 0;
    end
  endtask

  `define OTP_ASSERT_WO_LC_ESC(NAME, SEQ) \
    `ASSERT(NAME, SEQ, clk_i, !rst_ni || lc_esc_on || alert_reqs)

  // If pwr_otp_idle is set only if pwr_otp init is done
  `OTP_ASSERT_WO_LC_ESC(OtpPwrDoneWhenIdle_A, pwr_otp_idle_o |-> pwr_otp_done_o)

  // Otp_hw_cfg_o is valid only when otp init is done
  `OTP_ASSERT_WO_LC_ESC(OtpHwCfgValidOn_A, pwr_otp_done_o |->
                        otp_hw_cfg_o.valid == lc_ctrl_pkg::On)
  // If otp_hw_cfg is Off, then hw partition is not finished calculation, then otp init is not done
  `OTP_ASSERT_WO_LC_ESC(OtpHwCfgValidOff_A, otp_hw_cfg_o.valid == lc_ctrl_pkg::Off |->
                        pwr_otp_done_o == 0)
  // Once OTP init is done, hw_cfg_o output value stays stable until next power cycle
  `OTP_ASSERT_WO_LC_ESC(OtpHwCfgStable_A, otp_hw_cfg_o.valid == lc_ctrl_pkg::On |=>
                        $stable(otp_hw_cfg_o))

  // Otp_keymgr valid is related to part_digest, should not be changed after otp_pwr_init
  `OTP_ASSERT_WO_LC_ESC(OtpKeymgrValidStable_A, pwr_otp_done_o |-> $stable(keymgr_key_o.valid))

  // During lc_prog_req, either otp_idle will be reset or lc_error is set
  `OTP_ASSERT_WO_LC_ESC(LcProgReq_A, $rose(lc_prog_req) |=>
                       (pwr_otp_idle_o == 0 || $rose(lc_prog_err)) within lc_prog_req[*1:$])

  // TODO: add assertions when esc_en is On
  `undef OTP_ASSERT_WO_LC_ESC
  `undef ECC_REG_PATH
endinterface
