// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to probe Ibex RVFI interface
interface core_ibex_rvfi_if(input logic clk);
  logic        reset;
  logic        valid;
  logic [63:0] order;
  logic [31:0] insn;
  logic        trap;
  logic        halt;
  logic        intr;
  logic [1:0]  mode;
  logic [1:0]  ixl;
  logic [4:0]  rs1_addr;
  logic [4:0]  rs2_addr;
  logic [31:0] rs1_rdata;
  logic [31:0] rs2_rdata;
  logic [4:0]  rd_addr;
  logic [31:0] rd_wdata;
  logic [31:0] pc_rdata;
  logic [31:0] pc_wdata;
  logic [31:0] mem_addr;
  logic [3:0]  mem_rmask;
  logic [3:0]  mem_wmask;
  logic [31:0] mem_rdata;
  logic [31:0] mem_wdata;
  logic [31:0] ext_mip;
  logic        ext_nmi;
  logic [31:0] ext_debug_req;
  logic [63:0] ext_mcycle;

  clocking monitor_cb @(posedge clk);
    input reset;
    input valid;
    input order;
    input insn;
    input trap;
    input halt;
    input intr;
    input mode;
    input ixl;
    input rs1_addr;
    input rs2_addr;
    input rs1_rdata;
    input rs2_rdata;
    input rd_addr;
    input rd_wdata;
    input pc_rdata;
    input pc_wdata;
    input mem_addr;
    input mem_rmask;
    input mem_wmask;
    input mem_rdata;
    input mem_wdata;
    input ext_mip;
    input ext_nmi;
    input ext_debug_req;
    input ext_mcycle;
  endclocking

  task automatic wait_clks(input int num);
    repeat (num) @(posedge clk);
  endtask
endinterface
