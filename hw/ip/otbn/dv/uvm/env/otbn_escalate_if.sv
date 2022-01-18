// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// A one-signal interface for escalation signals

interface otbn_escalate_if (
  input logic clk_i,
  input logic rst_ni
);

  lc_ctrl_pkg::lc_tx_t enable;

endinterface
