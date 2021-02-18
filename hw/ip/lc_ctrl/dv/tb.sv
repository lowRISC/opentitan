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
  import otp_ctrl_pkg::*;
  import jtag_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [LcPwrIfWidth-1:0] pwr_lc;
  // TODO: can delete once push-pull agent support constraint data
  wire otp_ctrl_pkg::lc_otp_program_rsp_t otp_prog_rsp;
  wire otp_ctrl_pkg::lc_otp_token_rsp_t   otp_token_rsp;

  // interfaces
  clk_rst_if   clk_rst_if(.clk(clk), .rst_n(rst_n));
  pins_if      #(1) devmode_if(devmode);
  pins_if      #(LcPwrIfWidth) pwr_lc_if(pwr_lc);
  tl_if        tl_if(.clk(clk), .rst_n(rst_n));
  lc_ctrl_if   lc_ctrl_if(.clk(clk), .rst_n(rst_n));
  alert_esc_if esc_wipe_secrets_if(.clk(clk), .rst_n(rst_n));
  alert_esc_if esc_scrap_state_if(.clk(clk), .rst_n(rst_n));
  jtag_if      jtag_if();
  push_pull_if #(.HostDataWidth(OTP_PROG_HDATA_WIDTH), .DeviceDataWidth(OTP_PROG_DDATA_WIDTH))
               otp_prog_if(.clk(clk), .rst_n(rst_n));
  push_pull_if #(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)) otp_token_if(.clk(clk), .rst_n(rst_n));

  `DV_ALERT_IF_CONNECT

  // TODO: remove once OTP_PROG_DDATA_WIDTH is set to 1
  assign otp_prog_rsp.err = lc_ctrl_if.prog_err;
  assign otp_prog_rsp.ack = otp_prog_if.ack;
  assign otp_token_rsp.ack = otp_token_if.ack;
  // TODO: temp constraint to 0 because it has to equal to otp_lc_data_i tokens
  assign otp_token_rsp.hashed_token = lc_ctrl_if.hashed_token;

  // dut
  lc_ctrl dut (
    .clk_i                      (clk      ),
    .rst_ni                     (rst_n    ),

    .tl_i                       (tl_if.h2d),
    .tl_o                       (tl_if.d2h),
    .alert_rx_i                 (alert_rx ),
    .alert_tx_o                 (alert_tx ),

    .jtag_i                     ({jtag_if.tck, jtag_if.tms, jtag_if.trst_n, jtag_if.tdi}),
    .jtag_o                     ({jtag_if.tdo, lc_ctrl_if.tdo_oe}),
    .scanmode_i                 (1'b0     ),

    .esc_wipe_secrets_tx_i      (esc_wipe_secrets_if.esc_tx),
    .esc_wipe_secrets_rx_o      (esc_wipe_secrets_if.esc_rx),
    .esc_scrap_state_tx_i       (esc_scrap_state_if.esc_tx),
    .esc_scrap_state_rx_o       (esc_scrap_state_if.esc_rx),

    .pwr_lc_i                   (pwr_lc[LcPwrInitReq]),
    .pwr_lc_o                   (pwr_lc[LcPwrDoneRsp:LcPwrIdleRsp]),

    .lc_otp_program_o           ({otp_prog_if.req, otp_prog_if.h_data}),
    .lc_otp_program_i           (otp_prog_rsp),

    .lc_otp_token_o             ({otp_token_if.req, otp_token_if.h_data}),
    .lc_otp_token_i             (otp_token_rsp),

    .otp_lc_data_i              (lc_ctrl_if.otp_i),

    .lc_dft_en_o                (lc_ctrl_if.lc_dft_en_o),
    .lc_nvm_debug_en_o          (lc_ctrl_if.lc_nvm_debug_en_o),
    .lc_hw_debug_en_o           (lc_ctrl_if.lc_hw_debug_en_o),
    .lc_cpu_en_o                (lc_ctrl_if.lc_cpu_en_o),
    .lc_creator_seed_sw_rw_en_o (lc_ctrl_if.lc_creator_seed_sw_rw_en_o),
    .lc_owner_seed_sw_rw_en_o   (lc_ctrl_if.lc_owner_seed_sw_rw_en_o),
    .lc_iso_part_sw_rd_en_o     (lc_ctrl_if.lc_iso_part_sw_rd_en_o),
    .lc_iso_part_sw_wr_en_o     (lc_ctrl_if.lc_iso_part_sw_wr_en_o),
    .lc_seed_hw_rd_en_o         (lc_ctrl_if.lc_seed_hw_rd_en_o),
    .lc_keymgr_en_o             (lc_ctrl_if.lc_keymgr_en_o),
    .lc_escalate_en_o           (lc_ctrl_if.lc_escalate_en_o),
    .lc_check_byp_en_o          (lc_ctrl_if.lc_check_byp_en_o),

    .lc_clk_byp_req_o           (lc_ctrl_if.clk_byp_req_o),
    .lc_clk_byp_ack_i           (lc_ctrl_if.clk_byp_ack_i),

    .lc_flash_rma_seed_o        (lc_ctrl_if.flash_rma_seed_o),
    .lc_flash_rma_req_o         (lc_ctrl_if.flash_rma_req_o),
    .lc_flash_rma_ack_i         (lc_ctrl_if.flash_rma_ack_i),

    .lc_keymgr_div_o            (lc_ctrl_if.keymgr_div_o),

    .otp_hw_cfg_i               (lc_ctrl_if.otp_hw_cfg_i)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(pwr_lc_vif)::set(null, "*.env", "pwr_lc_vif", pwr_lc_if);
    uvm_config_db#(virtual lc_ctrl_if)::set(null, "*.env", "lc_ctrl_vif", lc_ctrl_if);
    uvm_config_db#(virtual jtag_if)::set(null, "*env.m_jtag_agent*", "vif", jtag_if);

    uvm_config_db#(virtual alert_esc_if)::set(null, "*env.m_esc_wipe_secrets_agent*", "vif",
                                              esc_wipe_secrets_if);
    uvm_config_db#(virtual alert_esc_if)::set(null, "*env.m_esc_scrap_state_agent*", "vif",
                                              esc_scrap_state_if);

    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                                         .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)))::
                   set(null, "*env.m_otp_prog_pull_agent*", "vif", otp_prog_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(lc_ctrl_state_pkg::LcTokenWidth)))::
                   set(null, "*env.m_otp_token_pull_agent*", "vif", otp_token_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
