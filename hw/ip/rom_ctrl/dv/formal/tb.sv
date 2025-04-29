// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for rom_ctrl
// Intended to be used with a formal tool.

module tb
  import rom_ctrl_reg_pkg::NumAlerts;
  import prim_rom_pkg::rom_cfg_t;
(
  input  clk_i,
  input  rst_ni,
  input  rom_cfg_t rom_cfg_i,

  input  tlul_pkg::tl_h2d_t rom_tl_i,
  output tlul_pkg::tl_d2h_t rom_tl_o,

  input  tlul_pkg::tl_h2d_t regs_tl_i,
  output tlul_pkg::tl_d2h_t regs_tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Connections to other blocks
  output rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data_o,
  output rom_ctrl_pkg::keymgr_data_t keymgr_data_o,
  input  kmac_pkg::app_rsp_t         kmac_data_i,
  output kmac_pkg::app_req_t         kmac_data_o
 );

  rom_ctrl dut (
    .clk_i,
    .rst_ni,
    .rom_cfg_i,
    .rom_tl_i,
    .rom_tl_o,
    .regs_tl_i,
    .regs_tl_o,
    .alert_rx_i,
    .alert_tx_o,
    .pwrmgr_data_o,
    .keymgr_data_o,
    .kmac_data_i,
    .kmac_data_o
  );

  // We don't want to spend time thinking about the security of write addresses: there's actually
  // only one writable register (and it doesn't matter if someone forges a write to ALERT_TEST
  // anyway). Check that no change to the design stops this from being true.
  `ASSERT(SingleWritableReg_A,
          dut.u_reg_regs.reg_we_check ->
          dut.u_reg_regs.reg_addr == rom_ctrl_reg_pkg::ROM_CTRL_ALERT_TEST_OFFSET)

  // The prim_count module has logic to saturate if asked to count past its maximum (so long as that
  // maximum is 2^n-1 where n is the width of the counter). The rom_ctrl_compare module that uses
  // prim_count to run through the digests doesn't use that feature: in fact, it only passes
  // incr_en_i when not at the maximum.
  //
  // One advantage of this is that the digest length needn't be a power of two. A disadvantage is
  // that we will never ask for an increment that would saturate. As a result, the preconditions for
  // UpCntIncrStable_A and DnCntIncrStable_A are both impossible. Their coverage properties are
  // disabled in verify.tcl but these assertions check that the gating in rom_ctrl_compare really
  // does work as expected.
  `ASSERT(CompareCountNoSaturateUp_A,
          dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.u_prim_count_addr.incr_en_i ->
          !&dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.u_prim_count_addr.cnt_o)
  `ASSERT(CompareCountNoSaturateDn_A,
          dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.u_prim_count_addr.incr_en_i ->
          |dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.u_prim_count_addr.cnt_q[1])
endmodule
