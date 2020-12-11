// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import lc_ctrl_env_pkg::*;
  import lc_ctrl_test_pkg::*;
  import lc_ctrl_pkg::*;
  import otp_ctrl_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [LcPwrIfWidth-1:0] pwr_lc;
  // TODO: use push-pull agent
  wire lc_otp_token_rsp_t lc_rsp;
  assign lc_rsp.ack = 1;
  // TODO: temp constraint to 0 because it has to equal to otp_lc_data_i tokens
  assign lc_rsp.hashed_token = 0;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if #(1) devmode_if(devmode);
  pins_if #(LcPwrIfWidth) pwr_lc_if(pwr_lc);
  tl_if tl_if(.clk(clk), .rst_n(rst_n));
  lc_ctrl_if lc_ctrl_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // dut
  lc_ctrl dut (
    .clk_i                 (clk      ),
    .rst_ni                (rst_n    ),

    .tl_i                  (tl_if.h2d),
    .tl_o                  (tl_if.d2h),
    .alert_rx_i            (alert_rx ),
    .alert_tx_o            (alert_tx ),

    .jtag_i                (0),
    .jtag_o                (),

    .esc_wipe_secrets_tx_i ({2'b01}),
    .esc_wipe_secrets_rx_o (),
    .esc_scrap_state_tx_i  ({2'b01}),
    .esc_scrap_state_rx_o  (),

    .pwr_lc_i              (pwr_lc[LcPwrInitReq]),
    .pwr_lc_o              (pwr_lc[LcPwrDoneRsp:LcPwrIdleRsp]),

    .lc_otp_program_o      (),
    .lc_otp_program_i      ('b01),

    .lc_otp_token_o        (),
    .lc_otp_token_i        (lc_rsp),

    .otp_lc_data_i         (lc_ctrl_if.otp_i),

    .lc_dft_en_o           (),
    .lc_nvm_debug_en_o     (),
    .lc_hw_debug_en_o      (),
    .lc_cpu_en_o           (),
    .lc_keymgr_en_o        (),
    .lc_escalate_en_o      (),

    .lc_clk_byp_req_o      (),
    .lc_clk_byp_ack_i      (lc_ctrl_pkg::On),

    .lc_flash_rma_seed_o   (),
    .lc_flash_rma_req_o    (),
    .lc_flash_rma_ack_i    (lc_ctrl_pkg::Off),

    .otp_hw_cfg_i          (0)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(pwr_lc_vif)::set(null, "*.env", "pwr_lc_vif", pwr_lc_if);
    uvm_config_db#(virtual lc_ctrl_if)::set(null, "*.env", "lc_ctrl_vif", lc_ctrl_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
