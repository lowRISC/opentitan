// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface implements liveness assertions for sha3pad.
interface sha3pad_assert_if # (
    parameter bit EnMasking = 1
  )(
    input                      clk_i,
    input                      rst_ni,
    input logic                process_i,
    input logic                keccak_complete_i,
    input logic                keccak_run_o,
    input lc_ctrl_pkg::lc_tx_t lc_escalate_en_i
   );

  localparam int Share = (EnMasking) ? 2 : 1;

  // If `process_i` is asserted, eventually sha3pad trigger run signal
  `ASSERT(ProcessToRun_A, process_i |-> strong(##[2:$] keccak_run_o),
    clk_i, !rst_ni || lc_escalate_en_i != lc_ctrl_pkg::Off)

  // Keccak control interface
  // Keccak run triggered -> completion should come
  `ASSUME(RunThenComplete_M,
    keccak_run_o |-> strong(##[24*Share:$] keccak_complete_i),
    clk_i, !rst_ni || lc_escalate_en_i != lc_ctrl_pkg::Off)
endinterface
