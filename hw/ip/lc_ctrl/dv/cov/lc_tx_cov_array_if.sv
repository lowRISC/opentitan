// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This is essentially the same as cip_lc_tx_cov_if, except that it allows a bundle of lc_tx values
// in a single port and instantiates a copy of cip_lc_tx_cov_if for each.

interface lc_tx_cov_array_if #(parameter int Count = 1) (input [4*Count - 1:0] val, input rst_ni);
  for (genvar i = 0; i < Count; i++) begin : gen_connect_lc_tx_items
    cip_lc_tx_cov_if lc_tx_if(.val(val[4*i+3:4*i]), .rst_ni(rst_ni));
  end
endinterface
