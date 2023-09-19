// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This assertions check a software controlled reset and its corresponding reset enable.
// The reset enable here means the output that goes to the alert handler indicating whether
// the reset is active.
interface rstmgr_sw_rst_sva_if (
  input logic clk_i,
  input logic rst_ni,
  input logic parent_rst_n,
  input logic ctrl_n,
  input logic rst_en,
  input logic rst_n
);
  parameter int RiseMin = 2;
  parameter int RiseMax = 12;

  bit disable_sva;

  logic rst_cause;
  always_comb rst_cause = !parent_rst_n || !ctrl_n;

  sequence CauseReadyOn_S;
    $rose(
        rst_cause
    ) ##1 rst_cause [* RiseMin];
  endsequence

  sequence CauseReadyOff_S;
    $fell(
        rst_cause
    ) ##1 !rst_cause [* RiseMin];
  endsequence

  `ASSERT(RstNOn_A, CauseReadyOn_S |=> ##[0:RiseMax-RiseMin] !rst_cause || !rst_n, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(RstNOff_A, CauseReadyOff_S |=> ##[0:RiseMax-RiseMin] rst_cause || rst_n, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(RstEnOn_A, CauseReadyOn_S |=> ##[0:RiseMax-RiseMin] !rst_cause || rst_en, clk_i,
          !rst_ni || disable_sva)
  `ASSERT(RstEnOff_A, CauseReadyOff_S |=> ##[0:RiseMax-RiseMin] rst_cause || !rst_en, clk_i,
          !rst_ni || disable_sva)
endinterface
