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
  import rram_ctrl_bkdr_util_pkg::rram_ctrl_bkdr_util;

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
  rram_ctrl_misc_io_if          misc_if       (.clk(clk_otp), .rst_n(rst_otp_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if       (interrupts);

  rram_ctrl_pkg::rram_macro_req_t rram_req;
  rram_ctrl_pkg::rram_macro_rsp_t rram_rsp;

  otp_ctrl_pkg::nvm_otp_key_req_t          otp_key_req;
  otp_ctrl_pkg::nvm_otp_key_rsp_t          otp_key_rsp;
  otp_ctrl_macro_pkg::otp_ctrl_macro_req_t otp_macro_req;
  otp_ctrl_macro_pkg::otp_ctrl_macro_rsp_t otp_macro_rsp;

  assign misc_if.otp_macro_rsp.ready            = otp_macro_rsp.ready;
  assign misc_if.otp_macro_rsp.rvalid           = otp_macro_rsp.rvalid;
  assign misc_if.otp_macro_rsp.rdata            = otp_macro_rsp.rdata;
  assign misc_if.otp_macro_rsp.err              = otp_macro_rsp.err;
  assign misc_if.otp_macro_rsp.fatal_lc_fsm_err = otp_macro_rsp.fatal_lc_fsm_err;
  assign misc_if.otp_macro_rsp.fatal_alert      = otp_macro_rsp.fatal_alert;
  assign misc_if.otp_macro_rsp.recov_alert      = otp_macro_rsp.recov_alert;

  assign otp_macro_req.valid = misc_if.otp_macro_req.valid;
  assign otp_macro_req.cmd   = misc_if.otp_macro_req.cmd;
  assign otp_macro_req.size  = misc_if.otp_macro_req.size;
  assign otp_macro_req.addr  = misc_if.otp_macro_req.addr;
  assign otp_macro_req.wdata = misc_if.otp_macro_req.wdata;

  assign misc_if.otp_key_req.addr_req = otp_key_req.addr_req;
  assign misc_if.otp_key_req.data_req = otp_key_req.data_req;

  assign otp_key_rsp.addr_ack   = misc_if.otp_key_rsp.addr_ack;
  assign otp_key_rsp.data_ack   = misc_if.otp_key_rsp.data_ack;
  assign otp_key_rsp.key        = misc_if.otp_key_rsp.key;
  assign otp_key_rsp.rand_key   = misc_if.otp_key_rsp.rand_key;
  assign otp_key_rsp.seed_valid = misc_if.otp_key_rsp.seed_valid;

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
    .otp_key_i  (otp_key_rsp),
    .otp_key_o  (otp_key_req),

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

    .keymgr_o(misc_if.keymgr),

    // power manager indication
    .pwrmgr_o(misc_if.pwr_nvm),

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
    .TotalPages(rram_ctrl_pkg::TotalPages),
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

  // Instantiate the memory backdoor util instances.
  //
  // This only applies to the generic rram. A unique memory backdoor util instance is created for
  // each type of rram partition.
  `define RRAM_DATA_MEM_HIER      tb.u_rram_macro.u_data_array.mem
  `define RRAM_DATA_MEM_HIER_STR  "tb.u_rram_macro.u_data_array.mem"
  `define RRAM_INFO_MEM_HIER      tb.u_rram_macro.u_info_array.mem
  `define RRAM_INFO_MEM_HIER_STR  "tb.u_rram_macro.u_info_array.mem"

  initial begin
    rram_ctrl_bkdr_util m_mem_bkdr_util;
    rram_ctrl_pkg::rram_part_e part = rram_ctrl_pkg::RramPartData;
    m_mem_bkdr_util = new(
      .name($sformatf("rram_ctrl_bkdr_util[%0s]", part.name())),
      .path(`RRAM_DATA_MEM_HIER_STR),
      .depth($size(`RRAM_DATA_MEM_HIER)),
      .n_bits($bits(`RRAM_DATA_MEM_HIER)),
      .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone)
    );
    uvm_config_db#(rram_ctrl_bkdr_util)::set(null, "*.env", m_mem_bkdr_util.get_name(),
                                             m_mem_bkdr_util);
  end

  initial begin
    rram_ctrl_bkdr_util m_mem_bkdr_util;
    rram_ctrl_pkg::rram_part_e part = rram_ctrl_pkg::RramPartInfo;
    m_mem_bkdr_util = new(
      .name($sformatf("rram_ctrl_bkdr_util[%0s]", part.name())),
      .path(`RRAM_INFO_MEM_HIER_STR),
      .depth($size(`RRAM_INFO_MEM_HIER)),
      .n_bits($bits(`RRAM_INFO_MEM_HIER)),
      .err_detection_scheme(mem_bkdr_util_pkg::ErrDetectionNone)
    );
    uvm_config_db#(rram_ctrl_bkdr_util)::set(null, "*.env", m_mem_bkdr_util.get_name(),
                                             m_mem_bkdr_util);
  end

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
    uvm_config_db#(misc_vif_t)::set(null, "*.env", "misc_vif", misc_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule : tb
