// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rv_dm_enable_checker
  import rv_dm_reg_pkg::NrHarts;
(
  input logic         clk_i,
  input logic         rst_ni,

  input lc_ctrl_pkg::lc_tx_t   lc_hw_debug_en_i,
  input lc_ctrl_pkg::lc_tx_t   lc_dft_en_i,
  input prim_mubi_pkg::mubi8_t otp_dis_rv_dm_late_debug_i,
  input logic [NrHarts-1:0]    debug_req_o_i,
  input tlul_pkg::tl_d2h_t     mem_tl_d_o_i,
  input tlul_pkg::tl_h2d_t     sba_tl_h_o_i,

  input logic                        ndmreset_ack,
  rv_dm_reg_pkg::rv_dm_regs_reg2hw_t regs_reg2hw
);

  import lc_ctrl_pkg::lc_tx_test_true_strict;
  import prim_mubi_pkg::mubi8_test_true_strict;
  import prim_mubi_pkg::mubi32_test_true_strict;

  // This is the signal that governs whether "late debug enable" is in force (true if set by a
  // top-level pin with the otp_dis_* signal or if set by a register, visible from regs_reg2hw)
  logic late_debug_enable;
  assign late_debug_enable =
    mubi8_test_true_strict(otp_dis_rv_dm_late_debug_i) ||
    mubi32_test_true_strict(prim_mubi_pkg::mubi32_t'(regs_reg2hw.late_debug_enable));

  // Should debug be enabled? If we're using late_debug_enable, this is governed by
  // lc_hw_debug_en_i. If not, it comes from lc_dft_en_i.
  logic debug_enabled;
  assign debug_enabled = lc_tx_test_true_strict(late_debug_enable ? lc_hw_debug_en_i : lc_dft_en_i);

  // An ndmreset ack is only passed to the debug module if debug is enabled.
  `ASSERT(NdmResetAckNeedsDebug_A, ndmreset_ack |-> debug_enabled)

  // A debug request can only be passed from the debug module to the hart if debug is enabled
  `ASSERT(DebugRequestNeedsDebug_A, debug_req_o_i |-> debug_enabled)

  // If debug is not enabled then the mem TL interface is disabled and will respond to everything
  // with an error. This means that any response will have d_error=1.
  `ASSERT(MemTLResponseWithoutDebugIsError_A,
          mem_tl_d_o_i.d_valid && !debug_enabled |-> mem_tl_d_o_i.d_error)

  // If debug is not enabled then the SBA TL interface is disabled and we will never generate a new
  // TL transaction. As such, the a_valid signal will always be false.
  `ASSERT(SbaTLRequestNeedsDebug_A, sba_tl_h_o_i.a_valid |-> debug_enabled)
endmodule
