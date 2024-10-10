// Copyright lowRISC contributors (OpenTitan project).
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

  bit    en_cov = 0;

  logic  any_req;
  assign any_req = rd_req || prog_req || pg_erase_req || bk_erase_req;
  logic  any_vld_req;
  assign any_vld_req = any_req && ack;

  // Decode current command
  typedef enum logic[1:0] {READ, PROG, ERASE, NONE} cmd_e;
  cmd_e cur_cmd;
  always_comb begin
    cur_cmd = NONE;
    if (any_vld_req) begin
      if (rd_req) cur_cmd = READ;
      else if (prog_req) cur_cmd = PROG;
      else if (pg_erase_req || bk_erase_req) cur_cmd = ERASE;
    end
  end

  // previous command
  cmd_e prv_cmd_q;
  always @(posedge clk_i) begin
    if (!rst_ni) begin
      prv_cmd_q <= NONE;
    end else begin
      if (any_vld_req) begin
        prv_cmd_q <= cur_cmd;
      end
    end
  end

  // command interval counter
  // couter will be saturated when it hits maxium
  bit [31:0] idle_cnt;
  always @(posedge clk_i) begin
    if (!rst_ni || !rd_buf_en) idle_cnt <= 0;
    else idle_cnt <= (any_vld_req)? 0 :
                     (idle_cnt == 32'hffff_ffff)? 32'hffff_ffff : idle_cnt + 32'h1;
  end

  // back to back read sequence
  logic b2b_read;
  assign b2b_read = (cur_cmd == READ && prv_cmd_q == READ);

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
