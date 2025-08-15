// Copyright lowRISC contributors (OpenTitan project).
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
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts_soc;

  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_core_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_soc_if(.clk(clk), .rst_n(rst_n));
  tl_if tl_sram_if(.clk(clk), .rst_n(rst_n));
  pins_if #(NUM_MAX_INTERRUPTS) intr_core_if(interrupts);
  pins_if #(NUM_MAX_INTERRUPTS) intr_soc_if(interrupts_soc);

  `DV_ALERT_IF_CONNECT()

  // dut
  mbx #() dut
  (
    .clk_i(clk),
    .rst_ni(rst_n),
    .doe_intr_support_o(),
    .doe_intr_en_o(),
    .doe_intr_o(interrupts_soc[MbxSocDOE]),
    .doe_async_msg_support_o(),
    .racl_policies_i (top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    // various tlul interfaces
    .core_tl_d_o(tl_core_if.d2h),
    .core_tl_d_i(tl_core_if.h2d),
    .soc_tl_d_o(tl_soc_if.d2h),
    .soc_tl_d_i(tl_soc_if.h2d),
    .sram_tl_h_o(tl_sram_if.h2d),
    .sram_tl_h_i(tl_sram_if.d2h),
    // alerts and interrupts
    .intr_mbx_ready_o(interrupts[MbxCoreReady]),
    .intr_mbx_abort_o(interrupts[MbxCoreAbort]),
    .intr_mbx_error_o(interrupts[MbxCoreError]),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx)
  );

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif", clk_rst_if);

    // RoT-side configuration register interface.
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_core_reg_block", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbx_core_reg_block*", "vif", tl_core_if);
    // SoC-side configuration register interface.
    uvm_config_db#(virtual clk_rst_if)::set(
      null, "*.env", "clk_rst_vif_mbx_soc_reg_block", clk_rst_if);
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_mbx_soc_reg_block*", "vif", tl_soc_if);

    // RoT-side SRAM interface.
    uvm_config_db#(virtual tl_if)::set(
      null, "*.env.m_tl_agent_sram*", "vif", tl_sram_if);

    // RoT-side interrupt interface.
    uvm_config_db#(intr_vif)::set(
      null, "*.env", "intr_vif", intr_core_if);
    // SoC-side interrupt interface.
    uvm_config_db#(intr_vif)::set(
      null, "*.env", "intr_soc_vif", intr_soc_if);

    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
