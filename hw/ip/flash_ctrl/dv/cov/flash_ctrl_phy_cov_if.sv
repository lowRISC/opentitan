// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Sampling physical interface of the flash
// tb.dut.u_eflash.u_flash
import flash_ctrl_pkg::*;
interface flash_ctrl_phy_cov_if
(
  input logic        clk_i,
  input logic        rst_ni,
  input logic        rd_buf_en,
  input logic        rd_req,
  input logic        prog_req,
  input logic        pg_erase_req,
  input logic        bk_erase_req,
  input logic        ack,
  input logic [15:0] addr
);

  bit                en_cov = 0;
  typedef enum logic[1:0] {READ, PROG, ERASE, NONE} cmd_e;
  cmd_e cur_cmd, cur_cmd_d, prv_cmd;

  // read address for previous read command
  logic [15:0] prv_rd_addr, prv_rd_addr_d;
  // read address for current read command
  logic [15:0] rd_addr, rd_addr_d;
  logic  any_req;
  assign any_req = rd_req | prog_req | pg_erase_req | bk_erase_req;
  logic  any_vld_req;
  assign any_vld_req = any_req & ack;

  // command interval counter
  // couter will be saturated when it hits maxium
  bit [31:0] idle_cnt;

  function static cmd_e get_cmd;
    if (rd_req) return READ;
    if (prog_req) return PROG;
    if (pg_erase_req|bk_erase_req) return ERASE;
  endfunction

  assign cur_cmd = (any_vld_req)? get_cmd() : NONE;
  assign rd_addr = (cur_cmd == READ)? addr : rd_addr_d;
  assign prv_rd_addr = (cur_cmd != READ && cur_cmd_d == READ)? rd_addr : prv_rd_addr_d;

  always @(posedge clk_i) begin
    if (~rst_ni) begin
      cur_cmd_d <= NONE;
      rd_addr_d <= 'h0;
      prv_rd_addr_d <= 'h0;
      prv_cmd <= NONE;
    end else begin
      cur_cmd_d <= cur_cmd;
      rd_addr_d <= rd_addr;
      prv_rd_addr_d <= prv_rd_addr;
      prv_cmd <= (any_req & ack)? cur_cmd : prv_cmd;
    end
  end

  always @(posedge clk_i) begin
    if (~rst_ni| ~rd_buf_en) idle_cnt <= 0;
    else idle_cnt <= (any_req & ack)? 0 :
                     (idle_cnt == 32'hffff_ffff)? 32'hffff_ffff : idle_cnt + 32'h1;
  end

  // back to back read sequence
  logic b2b_read;
  assign b2b_read = (cur_cmd == READ && prv_cmd == READ);


  // Flash controller has read cache before the physical interface.
  // The cache returns data for the read address recorded in the cache.
  // Therefore, back to back same address read should not be shown on the physical interface.
  `ASSERT(NoSameAddrRead_A,
          cur_cmd == READ |-> prv_rd_addr != addr, clk_i,(~rst_ni | ~rd_buf_en))

  // Covergroup to sample read after any of {read,prog,erase} operations
  // Which was asked in #3353
  // Due to cache operation, all addresses for read after read are not the same.
  // Only exception is when eviction happens, which is captured in separate covergroup (eviction_cg)

  covergroup phy_rd_cg @(posedge any_vld_req);
    read_pat :
    coverpoint cur_cmd {
      bins any2read[] = (READ,PROG,ERASE => READ);
    }
  endgroup // phy_rd

  // Covergroup to sample interval of back to back read operation
  covergroup b2b_read_interval_cg @(posedge b2b_read);
    read_interval:
    coverpoint idle_cnt {
      bins duration[] = {1, [2:5], [5:9], [10:30], [31:99]};
      bins others = default;
    }
  endgroup

  initial begin
    phy_rd_cg phy_rd_cg_inst;
    b2b_read_interval_cg rd_intv_cg_inst;
    void'($value$plusargs("en_cov=%0b", en_cov));
    if (en_cov) begin
      phy_rd_cg_inst = new();
      rd_intv_cg_inst = new();
    end
  end
endinterface
