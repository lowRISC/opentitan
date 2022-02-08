// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_reg_pkg::*;
  import lc_ctrl_state_pkg::*;
  import lc_ctrl_env_pkg::*;
  import lc_ctrl_test_pkg::*;
  import otp_ctrl_pkg::*;
  import jtag_riscv_agent_pkg::*;

  // LC_CTRL parameters
  // Enable asynchronous transitions on alerts.
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}};
  // Idcode value for the JTAG.
  parameter logic [31:0] IdcodeValue = 32'h00000001;
  // Random netlist constants
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivInvalid    =
    LcKeymgrDivWidth'({(LcKeymgrDivWidth/8){32'h00000000}});
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivTestDevRma =
    LcKeymgrDivWidth'({(LcKeymgrDivWidth/8){8'h5a}});
  parameter lc_keymgr_div_t RndCnstLcKeymgrDivProduction =
    LcKeymgrDivWidth'({(LcKeymgrDivWidth/8){8'ha5}});

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire [LcPwrIfWidth-1:0] pwr_lc;

  wire [OtpTestCtrlWidth-1:0] otp_vendor_test_ctrl;
  wire [OtpTestStatusWidth-1:0] otp_vendor_test_status;
  assign lc_ctrl_if.otp_vendor_test_ctrl_o = otp_vendor_test_ctrl;
  assign otp_vendor_test_status = lc_ctrl_if.otp_vendor_test_status_i;

  // interfaces
  clk_rst_if clk_rst_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  pins_if #(1) devmode_if (devmode);
  pins_if #(LcPwrIfWidth) pwr_lc_if (pwr_lc);
  tl_if tl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  lc_ctrl_if lc_ctrl_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  alert_esc_if esc_scrap_state1_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  alert_esc_if esc_scrap_state0_if (
    .clk  (clk),
    .rst_n(rst_n)
  );
  jtag_if jtag_if ();
  push_pull_if #(
    .HostDataWidth  (OTP_PROG_HDATA_WIDTH),
    .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)
  ) otp_prog_if (
    .clk  (clk),
    .rst_n(rst_n)
  );


  // KMAC App agent hookup
  kmac_pkg::app_rsp_t kmac_data_in;
  kmac_pkg::app_req_t kmac_data_out;
  assign kmac_data_in = kmac_app_if.kmac_data_rsp;
  assign kmac_app_if.kmac_data_req = kmac_data_out;

  // KMAC vip
  kmac_app_intf kmac_app_if (
    .clk  (clk),
    .rst_n(rst_n)
  );

  `DV_ALERT_IF_CONNECT

  // dut
  lc_ctrl #(
    .AlertAsyncOn(AlertAsyncOn),
    // Idcode value for the JTAG.
    .IdcodeValue(IdcodeValue),
    // Random netlist constants
    .RndCnstLcKeymgrDivInvalid(RndCnstLcKeymgrDivInvalid),
    .RndCnstLcKeymgrDivTestDevRma(RndCnstLcKeymgrDivTestDevRma),
    .RndCnstLcKeymgrDivProduction(RndCnstLcKeymgrDivProduction)
  ) dut (
    .clk_i (clk),
    .rst_ni(rst_n),

    // TODO: connect this to a different clock
    .clk_kmac_i (clk),
    .rst_kmac_ni(rst_n),

    .tl_i      (tl_if.h2d),
    .tl_o      (tl_if.d2h),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx),

    .jtag_i     ({jtag_if.tck, jtag_if.tms, jtag_if.trst_n, jtag_if.tdi}),
    .jtag_o     ({jtag_if.tdo, lc_ctrl_if.tdo_oe}),
    .scanmode_i (lc_ctrl_if.scanmode_i),
    .scan_rst_ni(lc_ctrl_if.scan_rst_ni),

    .esc_scrap_state0_tx_i(esc_scrap_state0_if.esc_tx),
    .esc_scrap_state0_rx_o(esc_scrap_state0_if.esc_rx),
    .esc_scrap_state1_tx_i(esc_scrap_state1_if.esc_tx),
    .esc_scrap_state1_rx_o(esc_scrap_state1_if.esc_rx),

    .pwr_lc_i(pwr_lc[LcPwrInitReq]),
    .pwr_lc_o(pwr_lc[LcPwrDoneRsp:LcPwrIdleRsp]),

    .lc_otp_vendor_test_o(otp_vendor_test_ctrl),
    .lc_otp_vendor_test_i(otp_vendor_test_status),

    .lc_otp_program_o({otp_prog_if.req, otp_prog_if.h_data}),
    .lc_otp_program_i({otp_prog_if.d_data, otp_prog_if.ack}),

    .kmac_data_i(kmac_data_in),
    .kmac_data_o(kmac_data_out),

    .otp_lc_data_i(lc_ctrl_if.otp_i),

    .lc_dft_en_o               (lc_ctrl_if.lc_dft_en_o),
    .lc_nvm_debug_en_o         (lc_ctrl_if.lc_nvm_debug_en_o),
    .lc_hw_debug_en_o          (lc_ctrl_if.lc_hw_debug_en_o),
    .lc_cpu_en_o               (lc_ctrl_if.lc_cpu_en_o),
    .lc_creator_seed_sw_rw_en_o(lc_ctrl_if.lc_creator_seed_sw_rw_en_o),
    .lc_owner_seed_sw_rw_en_o  (lc_ctrl_if.lc_owner_seed_sw_rw_en_o),
    .lc_iso_part_sw_rd_en_o    (lc_ctrl_if.lc_iso_part_sw_rd_en_o),
    .lc_iso_part_sw_wr_en_o    (lc_ctrl_if.lc_iso_part_sw_wr_en_o),
    .lc_seed_hw_rd_en_o        (lc_ctrl_if.lc_seed_hw_rd_en_o),
    .lc_keymgr_en_o            (lc_ctrl_if.lc_keymgr_en_o),
    .lc_escalate_en_o          (lc_ctrl_if.lc_escalate_en_o),
    .lc_check_byp_en_o         (lc_ctrl_if.lc_check_byp_en_o),

    .lc_clk_byp_req_o(lc_ctrl_if.clk_byp_req_o),
    .lc_clk_byp_ack_i(lc_ctrl_if.clk_byp_ack_i),

    .lc_flash_rma_seed_o(lc_ctrl_if.flash_rma_seed_o),
    .lc_flash_rma_req_o (lc_ctrl_if.flash_rma_req_o),
    .lc_flash_rma_ack_i (lc_ctrl_if.flash_rma_ack_i),

    .lc_keymgr_div_o(lc_ctrl_if.keymgr_div_o),

    .otp_device_id_i(lc_ctrl_if.otp_device_id_i),

    .otp_manuf_state_i(lc_ctrl_if.otp_manuf_state_i)
  );

  //
  // Whitebox signals - these come from within the RTL
  //

  // JTAG/TL Mutex claim
  // Need a small delay to filter out glitches
  assign #1ps lc_ctrl_if.mutex_claim_jtag = (dut.tap_reg2hw.claim_transition_if.qe == 1) &&
      prim_mubi_pkg::mubi8_test_false_loose(
      dut.tap_claim_transition_if_q
  );

  assign #1ps lc_ctrl_if.mutex_claim_tl = (dut.reg2hw.claim_transition_if.qe == 1) &&
      prim_mubi_pkg::mubi8_test_false_loose(
      dut.sw_claim_transition_if_q
  );


  initial begin
    lc_ctrl_parameters_cfg parameters_cfg = lc_ctrl_parameters_cfg::type_id::create(
        "parameters_cfg"
    );
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(pwr_lc_vif)::set(null, "*.env", "pwr_lc_vif", pwr_lc_if);
    uvm_config_db#(virtual lc_ctrl_if)::set(null, "*.env", "lc_ctrl_vif", lc_ctrl_if);

    // verilog_format: off - avoid bad formatting
    // The jtag_agent is a low_level agent that configured inside jtag_riscv_agent.
    uvm_config_db#(virtual jtag_if)::set(null, "*.env.m_jtag_riscv_agent.m_jtag_agent*", "vif",
                                         jtag_if);
    uvm_config_db#(virtual alert_esc_if)::set(null, "*env.m_esc_scrap_state1_agent*", "vif",
                                              esc_scrap_state1_if);
    uvm_config_db#(virtual alert_esc_if)::set(null, "*env.m_esc_scrap_state0_agent*", "vif",
                                              esc_scrap_state0_if);
    uvm_config_db#(virtual push_pull_if#(.HostDataWidth(OTP_PROG_HDATA_WIDTH),
                                         .DeviceDataWidth(OTP_PROG_DDATA_WIDTH)))::
                   set(null, "*env.m_otp_prog_pull_agent*", "vif", otp_prog_if);
    uvm_config_db#(virtual kmac_app_intf)::set(null, "*.env.m_kmac_app_agent", "vif", kmac_app_if);

    // Parameter config object
    parameters_cfg.alert_async_on = AlertAsyncOn;
    parameters_cfg.id_code_value = IdcodeValue;
    parameters_cfg.keymgr_div_invalid = RndCnstLcKeymgrDivInvalid;
    parameters_cfg.keymgr_div_test_dev_rma = RndCnstLcKeymgrDivTestDevRma;
    parameters_cfg.keymgr_div_production = RndCnstLcKeymgrDivProduction;
    uvm_config_db#(lc_ctrl_parameters_cfg)::set(null, "*", "parameters_cfg", parameters_cfg);

    // verilog_format: on
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  // Assertion controls
  `DV_ASSERT_CTRL("OtpProgH_DataStableWhenBidirectionalAndReq_A",
                  otp_prog_if.H_DataStableWhenBidirectionalAndReq_A)
  `DV_ASSERT_CTRL("OtpProgReqHighUntilAck_A", otp_prog_if.ReqHighUntilAck_A)
  `DV_ASSERT_CTRL("OtpProgAckAssertedOnlyWhenReqAsserted_A",
                  otp_prog_if.AckAssertedOnlyWhenReqAsserted_A)
  `DV_ASSERT_CTRL(
      "KmacIfSyncReqAckAckNeedsReq",
      dut.u_lc_ctrl_kmac_if.u_prim_sync_reqack_data_in.u_prim_sync_reqack.SyncReqAckAckNeedsReq)
  `DV_ASSERT_CTRL(
      "KmacIfSyncReqAckAckNeedsReq",
      dut.u_lc_ctrl_kmac_if.u_prim_sync_reqack_data_out.u_prim_sync_reqack.SyncReqAckAckNeedsReq)
  `DV_ASSERT_CTRL("KmacIfSyncReqAckAckNeedsReq",
                  kmac_app_if.req_data_if.H_DataStableWhenValidAndNotReady_A)
  `DV_ASSERT_CTRL("KmacIfSyncReqAckAckNeedsReq", kmac_app_if.req_data_if.ValidHighUntilReady_A)

endmodule
