// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface pattgen_if #(
  parameter int unsigned NumChannels = 2
);
  logic clk_i;
  logic rst_ni;

  // standard pattgen interface pins
  logic [NumChannels-1:0] pda_tx;
  logic [NumChannels-1:0] pcl_tx;

endinterface : pattgen_if

