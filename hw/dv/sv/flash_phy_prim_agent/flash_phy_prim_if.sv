// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface flash_phy_prim_if (
  input logic clk,
  input logic rst_n
);
  import flash_phy_pkg::*;

  flash_phy_prim_flash_req_t [NumBanks-1:0] req;
  flash_phy_prim_flash_rsp_t [NumBanks-1:0] rsp;

  clocking cb @(posedge clk);
    input     req, rsp;
  endclocking
endinterface
