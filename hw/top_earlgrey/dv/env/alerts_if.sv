// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface samples alerts to enable coverage of alerts triggered.
interface alerts_if (
  input logic clk,
  input logic rst_ni,
  input logic [alert_pkg::NAlerts-1:0] alerts
);

  clocking alerts_cb @(posedge clk);
    input alerts;
  endclocking
endinterface : alerts_if
