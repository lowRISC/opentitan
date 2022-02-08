// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for LC_CTRL
interface lc_ctrl_cov_if (
  input clk_i,
  input rst_ni
);
  int count;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) count = 0;
    else count++;
  end

endinterface
