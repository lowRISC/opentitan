// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This interface is used to sample some csr values directly from the rtl
// to avoid any confusion.

interface clkmgr_csrs_if (
  input logic clk,
  input logic [10:0] recov_err_csr,
  input logic [2:0] fatal_err_csr,
  input logic [3:0] clk_enables,
  input logic [3:0] clk_hints
);

clocking csrs_cb @(posedge clk);
  input recov_err_csr;
  input fatal_err_csr;
  input clk_enables;
  input clk_hints;
endclocking

endinterface : clkmgr_csrs_if
