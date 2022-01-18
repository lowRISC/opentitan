// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This contains SVA assertions for clock gating output to alert_handler for
// AON clocks: they are never gated off.
interface clkmgr_aon_cg_en_sva_if (
  input logic clk,
  input logic rst_n,
  input logic cg_en
);

  bit disable_sva;

  `ASSERT_INIT_NET(CgEn_A, !cg_en)
endinterface
