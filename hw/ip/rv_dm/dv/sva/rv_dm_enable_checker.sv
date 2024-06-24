// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rv_dm_enable_checker
  import rv_dm_reg_pkg::NrHarts;
(
  input logic         clk_i,
  input logic         rst_ni,

  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input logic [NrHarts-1:0]  debug_req_o_i,
  input tlul_pkg::tl_d2h_t   mem_tl_d_o_i,
  input tlul_pkg::tl_h2d_t   sba_tl_h_o_i,

  input logic                ndmreset_ack
);

  import lc_ctrl_pkg::lc_tx_test_true_strict;

  // An ndmreset ack is only passed to the debug module if debug is enabled.
  `ASSERT(NdmResetAckNeedsDebug_A,
          ndmreset_ack |-> lc_tx_test_true_strict(lc_hw_debug_en_i))

  // A debug request can only be passed from the debug module to the hart if debug is enabled
  `ASSERT(DebugRequestNeedsDebug_A,
          debug_req_o_i |-> lc_tx_test_true_strict(lc_hw_debug_en_i))

  // If debug is not enabled then the mem TL interface is disabled and will respond to everything
  // with an error. This means that any response will have d_error=1.
  `ASSERT(MemTLResponseWithoutDebugIsError_A,
          mem_tl_d_o_i.d_valid && !lc_tx_test_true_strict(lc_hw_debug_en_i) |->
          mem_tl_d_o_i.d_error)

  // If debug is not enabled then the SBA TL interface is disabled and we will never generate a new
  // TL transaction. As such, the a_valid signal will always be false.
  `ASSERT(SbaTLRequestNeedsDebug_A,
          sba_tl_h_o.a_valid |-> lc_tx_test_true_strict(lc_hw_debug_en_i))
endmodule
