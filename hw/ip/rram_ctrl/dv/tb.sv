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
  import rram_ctrl_bkdr_util_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  // Defines `RRAM_DATA_MEM_PATH`/`RRAM_INFO_MEM_PATH`, resolved to whichever rram_ctrl_bkdr_util
  // implementation is mapped in.
  `include "rram_ctrl_bkdr_util_hier.svh"

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
  rram_ctrl_otp_macro_if        otp_macro_if  (.clk(clk_otp), .rst_n(rst_otp_n));
  rram_ctrl_misc_io_if          misc_if       (.clk(clk),     .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if       (interrupts);

  rram_ctrl_pkg::rram_macro_req_t rram_req;
  rram_ctrl_pkg::rram_macro_rsp_t rram_rsp;

  `DV_ALERT_IF_CONNECT()

  // Write/read FIFO depths, mirroring rram_ctrl's WrFifoDepth/RdFifoDepth RTL parameters.
  // Passed to the environment below via uvm_config_db.
  localparam int unsigned WrFifoDepth = 4;
  localparam int unsigned RdFifoDepth = 16;

  // DUT
  rram_ctrl #(
    .WrFifoDepth(WrFifoDepth),
    .RdFifoDepth(RdFifoDepth)
  ) dut (
    // main clock
    .clk_i (clk),
    .rst_ni(rst_n),
    // clocks for connections to otp_ctrl
    .clk_otp_i (clk_otp),
    .rst_otp_ni(rst_otp_n),

    // various tlul interfaces
    .core_tl_i(tl_core_if.h2d),
    .core_tl_o(tl_core_if.d2h),
    .host_tl_i(tl_host_if.h2d),
    .host_tl_o(tl_host_if.d2h),

    // otp interface
    .otp_macro_i(otp_macro_if.req),
    .otp_macro_o(otp_macro_if.rsp),
    .otp_key_i  (otp_key_if.otp_key_rsp),
    .otp_key_o  (otp_key_if.otp_key_req),

    // various life cycle decode signals
    .lc_creator_seed_sw_rw_en_i(misc_if.lc_creator_seed_sw_rw_en),
    .lc_owner_seed_sw_rw_en_i  (misc_if.lc_owner_seed_sw_rw_en),
    .lc_iso_part_sw_rd_en_i    (misc_if.lc_iso_part_sw_rd_en),
    .lc_iso_part_sw_wr_en_i    (misc_if.lc_iso_part_sw_wr_en),
    .lc_seed_hw_rd_en_i        (misc_if.lc_seed_hw_rd_en),
    .lc_escalate_en_i          (misc_if.lc_escalate_en),

    // life cycle rma handling
    .rma_req_i (misc_if.rma_req),
    .rma_seed_i(misc_if.rma_seed),
    .rma_ack_o (misc_if.rma_ack),

    // seeds for keymgr_dpe
    .keymgr_creator_seed_o(misc_if.keymgr_creator_seed),
    .keymgr_owner_seed_o  (misc_if.keymgr_owner_seed),

    // power manager indication
    .pwrmgr_o(misc_if.pwrmgr),

    // alerts and interrupts
    .intr_wr_empty_o (interrupts[WrEmpty]),
    .intr_wr_lvl_o   (interrupts[WrLvl]),
    .intr_rd_full_o  (interrupts[RdFull]),
    .intr_rd_lvl_o   (interrupts[RdLvl]),
    .intr_op_done_o  (interrupts[OpDone]),
    .intr_corr1_err_o(interrupts[Corr1Err]),
    .intr_corr2_err_o(interrupts[Corr2Err]),
    .alert_rx_i      (alert_rx),
    .alert_tx_o      (alert_tx),

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
    .lc_nvm_debug_en_i  (misc_if.lc_nvm_debug_en),
    .scanmode_i         (prim_mubi_pkg::MuBi4False),
    .scan_en_i          (1'b0),
    .scan_rst_ni        (1'b0),
    .rram_test_analog_io(rram_test_analog),
    .prim_tl_i          (tl_prim_if.h2d),
    .prim_tl_o          (tl_prim_if.d2h),
    .obs_ctrl_i         ('0),
    .rram_obs_o         ()
  );

  // TODO(#31287): connect to something meaningful
  assign (pull1, pull0) rram_test_analog = 1'b0;

  // Backdoor access to the RRAM arrays. Unlike the chip testbench, the data array utility covers
  // the OTP pages too, so that tests can check the OTP integrity page.
  `define RRAM_DATA_MEM_HIER u_rram_macro.`RRAM_DATA_MEM_PATH
  `define RRAM_INFO_MEM_HIER u_rram_macro.`RRAM_INFO_MEM_PATH

  initial begin
    // Xcelium does not understand typed constructors, so assign to local variables first.
    rram_ctrl_bkdr_util     data, info;
    rram_ctrl_otp_bkdr_util otp;

    data = new(.name                ("data_bkdr_util"),
               .path                (`DV_STRINGIFY(tb.`RRAM_DATA_MEM_HIER)),
               .depth               ($size(`RRAM_DATA_MEM_HIER)),
               .n_bits              ($bits(`RRAM_DATA_MEM_HIER)),
               .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone));
    info = new(.name                ("info_bkdr_util"),
               .path                (`DV_STRINGIFY(tb.`RRAM_INFO_MEM_HIER)),
               .depth               ($size(`RRAM_INFO_MEM_HIER)),
               .n_bits              ($bits(`RRAM_INFO_MEM_HIER)),
               .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone));
    otp  = new(.name                ("otp_bkdr_util"),
               .path                (`DV_STRINGIFY(tb.`RRAM_DATA_MEM_HIER)),
               .depth               ($size(`RRAM_DATA_MEM_HIER)),
               .n_bits              ($bits(`RRAM_DATA_MEM_HIER)),
               .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone));
    uvm_config_db#(rram_ctrl_bkdr_util)::set(null, "*.env", data.get_name(), data);
    uvm_config_db#(rram_ctrl_bkdr_util)::set(null, "*.env", info.get_name(), info);
    uvm_config_db#(rram_ctrl_otp_bkdr_util)::set(null, "*.env", otp.get_name(), otp);
  end

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
    uvm_config_db#(otp_key_vif_t)::set(null, "*.env.m_otp_*_key_driver", "otp_key_vif",
                                        otp_key_if);
    uvm_config_db#(misc_vif_t)::set(null, "*.env", "misc_vif", misc_if);
    uvm_config_db#(otp_macro_vif_t)::set(null, "*.env", "otp_macro_vif", otp_macro_if);
    uvm_config_db#(int unsigned)::set(null, "*.env", "WrFifoDepth", WrFifoDepth);
    uvm_config_db#(int unsigned)::set(null, "*.env", "RdFifoDepth", RdFifoDepth);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule : tb
