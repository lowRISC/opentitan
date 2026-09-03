// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module tb;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rram_ctrl_env_pkg::*;
  import rram_ctrl_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire                          clk;
  wire                          rst_n;
  wire                          clk_otp;
  wire                          rst_otp_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire                          rram_test_analog;

  // Interfaces
  clk_rst_if                    clk_rst_if    (.clk(clk),     .rst_n(rst_n));
  clk_rst_if                    otp_clk_rst_if(.clk(clk_otp), .rst_n(rst_otp_n));
  tl_if                         tl_core_if    (.clk(clk),     .rst_n(rst_n));
  tl_if                         tl_host_if    (.clk(clk),     .rst_n(rst_n));
  tl_if                         tl_prim_if    (.clk(clk),     .rst_n(rst_n));
  rram_ctrl_otp_key_if          otp_key_if    (.clk(clk_otp), .rst_n(rst_otp_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if       (interrupts);

  rram_ctrl_pkg::rram_macro_req_t rram_req;
  rram_ctrl_pkg::rram_macro_rsp_t rram_rsp;

  otp_ctrl_macro_pkg::otp_ctrl_macro_req_t otp_macro_req;
  otp_ctrl_macro_pkg::otp_ctrl_macro_rsp_t otp_macro_rsp;

  // Not driven by anything real yet - the DUT never sees a macro response.
  assign otp_macro_req = '{valid: 1'b0, cmd: otp_ctrl_macro_pkg::Init, default: '0};

  `DV_ALERT_IF_CONNECT()

  // DUT
  rram_ctrl #(
    .WrFifoDepth(rram_ctrl_env_pkg::WrFifoDepth),
    .RdFifoDepth(rram_ctrl_env_pkg::RdFifoDepth)
  ) dut (
    .clk_i          (clk),
    .rst_ni         (rst_n),

    .clk_otp_i      (clk_otp),
    .rst_otp_ni     (rst_otp_n),

    // various tlul interfaces
    .core_tl_i(tl_core_if.h2d),
    .core_tl_o(tl_core_if.d2h),
    .host_tl_i(tl_host_if.h2d),
    .host_tl_o(tl_host_if.d2h),

    // otp interface
    .otp_macro_i(otp_macro_req),
    .otp_macro_o(otp_macro_rsp),
    .otp_key_i  (otp_key_if.otp_key_rsp),
    .otp_key_o  (otp_key_if.otp_key_req),

    // various life cycle decode signals - fixed, not exercised by any test yet
    .lc_creator_seed_sw_rw_en_i(lc_ctrl_pkg::On),
    .lc_owner_seed_sw_rw_en_i  (lc_ctrl_pkg::On),
    .lc_iso_part_sw_rd_en_i    (lc_ctrl_pkg::On),
    .lc_iso_part_sw_wr_en_i    (lc_ctrl_pkg::On),
    .lc_seed_hw_rd_en_i        (lc_ctrl_pkg::Off),
    .lc_escalate_en_i          (lc_ctrl_pkg::Off),

    // life cycle rma handling - fixed, not exercised by any test yet
    .rma_req_i (lc_ctrl_pkg::Off),
    .rma_seed_i(lc_ctrl_pkg::LC_NVM_RMA_SEED_DEFAULT),
    .rma_ack_o (),

    .keymgr_o(),

    // power manager indication
    .pwrmgr_o(),

    // alerts and interrupts
    .intr_wr_empty_o  (interrupts[WrEmpty]),
    .intr_wr_lvl_o    (interrupts[WrLvl]),
    .intr_rd_full_o   (interrupts[RdFull]),
    .intr_rd_lvl_o    (interrupts[RdLvl]),
    .intr_op_done_o   (interrupts[OpDone]),
    .intr_corr_err_o  (interrupts[CorrErr]),
    .alert_rx_i       (alert_rx),
    .alert_tx_o       (alert_tx),

    .rram_macro_o(rram_req),
    .rram_macro_i(rram_rsp)
  );

  rram_macro #(
    .TotalDataPages(rram_ctrl_pkg::TotalDataPages),
    .DataWidth(rram_ctrl_pkg::DataWidth),
    .WordsPerPage(rram_ctrl_pkg::WordsPerPage),
    .TotalInfoPages(rram_ctrl_pkg::TotalInfoPages),
    .MaxWrWords(rram_ctrl_pkg::MaxWrWords)
  ) u_rram_macro (
    .clk_i              (clk),
    .rst_ni             (rst_n),
    .rram_macro_i       (rram_req),
    .rram_macro_o       (rram_rsp),
    .cio_tck_i          ('0),
    .cio_tdi_i          ('0),
    .cio_tms_i          ('0),
    .cio_tdo_o          (),
    .cio_tdo_en_o       (),
    .lc_nvm_debug_en_i  (lc_ctrl_pkg::Off),
    .scanmode_i         (prim_mubi_pkg::MuBi4False),
    .scan_en_i          (1'b0),
    .scan_rst_ni        (1'b0),
    .rram_test_analog_io(rram_test_analog),
    .prim_tl_i          (tl_prim_if.h2d),
    .prim_tl_o          (tl_prim_if.d2h),
    .obs_ctrl_i         ('0),
    .rram_obs_o         ()
  );

  // TODO: connect to something meaningful
  assign (pull1, pull0) rram_test_analog = 1'b0;

  initial begin
    otp_clk_rst_if.set_freq_mhz(OTP_CLK_FREQ_MHZ);
    clk_rst_if.set_active();
    otp_clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "otp_clk_rst_vif", otp_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_rram_ctrl_host_reg_block", clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_rram_macro_prim_reg_block", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_core*", "vif", tl_core_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_host*", "vif", tl_host_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent_*_prim*", "vif", tl_prim_if);
    uvm_config_db#(otp_key_vif_t)::set(null, "*.env", "otp_key_vif", otp_key_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule : tb
