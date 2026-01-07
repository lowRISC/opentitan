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

  // TODO, we should probably get this from a common pkg
  localparam WrFifoDepth = 4;
  localparam RdFifoDepth = 16;

  wire                          clk;
  wire                          rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire rram_test_analog;

  // Interfaces
  clk_rst_if                    clk_rst_if    (.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_if       (interrupts);
  tl_if                         tl_core_if    (.clk(clk), .rst_n(rst_n));
  tl_if                         tl_host_if    (.clk(clk), .rst_n(rst_n));
  tl_if                         tl_prim_if    (.clk(clk), .rst_n(rst_n));
  rram_ctrl_misc_io_if          misc_if       ();

  rram_ctrl_pkg::prim_rram_req_t rram_req;
  rram_ctrl_pkg::prim_rram_rsp_t rram_rsp;

  `DV_ALERT_IF_CONNECT()

  // DUT
  rram_ctrl #(
    .WrFifoDepth(WrFifoDepth),
    .RdFifoDepth(RdFifoDepth)
  ) dut (
    .clk_i          (clk),
    .rst_ni         (rst_n),

    .clk_otp_i      (clk),
    .rst_otp_ni     (rst_n),

    // various tlul interfaces
    .core_tl_i(tl_core_if.h2d),
    .core_tl_o(tl_core_if.d2h),
    .host_tl_i(tl_host_if.h2d),
    .host_tl_o(tl_host_if.d2h),

    // otp interface
    .otp_i('0),
    .otp_o(),

    // various life cycle decode signals
    .lc_creator_seed_sw_rw_en_i(lc_ctrl_pkg::On),
    .lc_owner_seed_sw_rw_en_i  (lc_ctrl_pkg::On),
    .lc_iso_part_sw_rd_en_i    (lc_ctrl_pkg::On),
    .lc_iso_part_sw_wr_en_i    (lc_ctrl_pkg::On),
    .lc_seed_hw_rd_en_i        (lc_ctrl_pkg::On),
    .lc_nvm_debug_en_i         (lc_ctrl_pkg::On),
    .lc_escalate_en_i          (lc_ctrl_pkg::On),

    // life cycle rma handling
    .rma_req_i (lc_ctrl_pkg::Off),
    .rma_seed_i('0),
    .rma_ack_o (),

    // power manager indication
    .pwrmgr_o(),
    .keymgr_o(),

    // alerts and interrupts
    .intr_wr_empty_o  (interrupts[WrEmpty]),
    .intr_wr_lvl_o    (interrupts[WrLvl]  ),
    .intr_rd_full_o   (interrupts[RdFull] ),
    .intr_rd_lvl_o    (interrupts[RdLvl]  ),
    .intr_op_done_o   (interrupts[OpDone] ),
    .intr_corr_err_o  (interrupts[CorrErr]),
    .alert_rx_i       (alert_rx),
    .alert_tx_o       (alert_tx),

    .prim_rram_req_o(rram_req),
    .prim_rram_rsp_i(rram_rsp)
  );

  rram_macro #(
    .TotalPages(rram_ctrl_pkg::TotalPages),
    .DataWidth(rram_ctrl_pkg::DataWidth),
    .WordsPerPage(rram_ctrl_pkg::WordsPerPage),
    .TotalInfoPages(rram_ctrl_pkg::TotalInfoPages),
    .WrResWords(rram_ctrl_pkg::WrResWords)
  ) u_rram_macro (
    .clk_i(clk),
    .rst_ni(rst_n),
    .rram_req_i(rram_req),
    .rram_rsp_o(rram_rsp),
    .init_busy_o(init_busy),
    .tck_i('0),
    .tdi_i('0),
    .tms_i('0),
    .tdo_o(),
    .bist_enable_i(prim_mubi_pkg::MuBi4False),
    .scanmode_i(prim_mubi_pkg::MuBi4False),
    .scan_en_i(1'b0),
    .scan_rst_ni(1'b0),
    .rram_test_analog_io(rram_test_analog),
    .fatal_alert_o(),
    .recov_alert_o(),
    .tl_i(tl_prim_if.h2d),
    .tl_o(tl_prim_if.d2h),
    .obs_ctrl_i('0),
    .rram_obs_o()
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
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
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
