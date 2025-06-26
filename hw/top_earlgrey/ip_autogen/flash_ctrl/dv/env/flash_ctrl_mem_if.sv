// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface flash_ctrl_mem_if (
  input logic clk_i,
  input logic rst_ni,
  input logic data_mem_req,
  input logic mem_wr,
  input logic [flash_phy_macro_pkg::BankAddrW-1:0] mem_addr,
  input logic [flash_phy_macro_pkg::DataWidth-1:0] mem_wdata,
  input flash_ctrl_pkg::flash_part_e mem_part,
  input logic [flash_phy_macro_pkg::InfoTypesWidth-1:0] mem_info_sel,
  input logic info0_mem_req,
  input logic info1_mem_req,
  input logic info2_mem_req
);
endinterface
