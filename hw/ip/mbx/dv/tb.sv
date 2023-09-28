// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import mbx_env_pkg::*;
  import mbx_test_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  `include "cip_macros.svh"

  wire clk, rst_n;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  wire intr_ready;
  wire intr_abort;

  clk_rst_if i_clk_rst_if(.clk(clk), .rst_n(rst_n));
  tl_if i_tl_scxb_mbx_core_if(.clk(clk), .rst_n(rst_n));
  tl_if i_tl_agxb_mbx_core_if(.clk(clk), .rst_n(rst_n));
  tl_if i_tl_mbx_agxb_device_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) i_intr_if(interrupts);

  `DV_ALERT_IF_CONNECT()

  // dut
  mbx #() dut
  (
    .clk_i(clk),
    .rst_ni(rst_n),
    .doe_intr_support_o(),
    .doe_intr_en_o(),
    .doe_intr_o(),
    // various tlul interfaces
    .core_tl_d_o(i_tl_agxb_mbx_core_if.d2h),
    .core_tl_d_i(i_tl_agxb_mbx_core_if.h2d),
    .soc_tl_d_o(i_tl_scxb_mbx_core_if.d2h),
    .soc_tl_d_i(i_tl_scxb_mbx_core_if.h2d),
    .sram_tl_h_o(i_tl_mbx_agxb_device_if.h2d),
    .sram_tl_h_i(i_tl_mbx_agxb_device_if.d2h),
    // alerts and interrupts
    .intr_mbx_ready_o(intr_ready),
    .intr_mbx_abort_o(intr_abort),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx)
  );

  // Connect the interrupts
  assign interrupts[MbxCoreReady] = intr_ready;
  assign interrupts[MbxCoreAbort] = intr_abort;

  initial begin
    // drive clk and rst_n from clk_if
    i_clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif", i_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_mem_reg_block", i_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_soc_reg_block", i_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_reg_block", i_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_core_reg_block", i_clk_rst_if);
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_soc_reg_block", i_clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbx_core_reg_block*", "vif",
      i_tl_agxb_mbx_core_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbx_soc_reg_block*", "vif",
      i_tl_scxb_mbx_core_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbxuarch_reg_block*", "vif",
      i_tl_agxb_mbx_core_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbx_reg_block*", "vif",
      i_tl_scxb_mbx_core_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbx_mem_reg_block*", "vif",
      i_tl_mbx_agxb_device_if);
    uvm_config_db#(intr_vif)::set(
      null, "*.env", "intr_vif", i_intr_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

  //FIXME: Previous reg_intf
  //mbx_reg_intf i_mbx_reg_intf(
  //  .clk(clk),
  //  .rst_n(rst_n),
  //  .req(i_tl_scxb_mbx_core_if.h2d),
  //  .rsp(i_tl_scxb_mbx_core_if.d2h)
  //);

  //mbxuarch_reg_intf i_mbxuarch_reg_intf(
  //  .clk(clk),
  //  .rst_n(rst_n),
  //  .req(i_tl_agxb_mbx_core_if.h2d),
  //  .rsp(i_tl_agxb_mbx_core_if.d2h)
  //);

endmodule
