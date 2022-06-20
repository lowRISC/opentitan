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
  // Inner read request / rdy
  logic [NumBanks-1:0] rreq;
  logic [NumBanks-1:0] rdy;

  // Debug tab
  flash_phy_prim_flash_req_t dreq0, dreq1;
  flash_phy_prim_flash_rsp_t drsp0, drsp1;

  assign dreq0 = req[0];
  assign drsp0 = rsp[0];
  assign dreq1 = req[1];
  assign drsp1 = rsp[1];

  clocking cb @(posedge clk);
    input     req, rsp, rreq, rdy;
  endclocking
endinterface
