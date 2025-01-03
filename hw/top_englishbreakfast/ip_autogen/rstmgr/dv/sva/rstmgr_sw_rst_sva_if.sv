// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has assertions that check the output resets read-only value of the alert and cpu_info_attr.
interface rstmgr_sw_rst_sva_if (
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] clk_i,
  input logic                                   rst_ni,
  input logic                                   parent_rst_n,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] ctrl_ns,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] rst_ens,
  input logic [rstmgr_reg_pkg::NumSwResets-1:0] rst_ns
);
  parameter int RiseMin = 2;
  parameter int RiseMax = 12;

  bit disable_sva;

  for (genvar i = 0; i < rstmgr_reg_pkg::NumSwResets; ++i) begin : gen_assertions
    logic rst_cause;
    always_comb rst_cause = !parent_rst_n || !ctrl_ns[i];

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

    `ASSERT(RstNOn_A, CauseReadyOn_S |=> ##[0:RiseMax-RiseMin] !rst_cause || !rst_ns[i], clk_i[i],
            !rst_ni || disable_sva)
    `ASSERT(RstNOff_A, CauseReadyOff_S |=> ##[0:RiseMax-RiseMin] rst_cause || rst_ns[i], clk_i[i],
            !rst_ni || disable_sva)
    `ASSERT(RstEnOn_A, CauseReadyOn_S |=> ##[0:RiseMax-RiseMin] !rst_cause || rst_ens[i], clk_i[i],
            !rst_ni || disable_sva)
    `ASSERT(RstEnOff_A, CauseReadyOff_S |=> ##[0:RiseMax-RiseMin] rst_cause || !rst_ens[i],
            clk_i[i], !rst_ni || disable_sva)
  end
endinterface
