// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ibex_icache_ram_if
  import ibex_pkg::*;
#(
  parameter int TagSizeECC = IC_TAG_SIZE,
  parameter int LineSizeECC = IC_LINE_BEATS * BUS_SIZE
) (
  input clk,
  input rst_n
);

logic [IC_INDEX_W-1:0]     ic_tag_addr;
logic                      ic_tag_write;
logic [IC_NUM_WAYS-1:0]    ic_tag_req;
logic [TagSizeECC-1:0]     ic_tag_wdata;
logic [IC_NUM_WAYS-1:0]    ic_tag_rvalid;
logic [TagSizeECC-1:0]     ic_tag_rdata_in [IC_NUM_WAYS];
logic [TagSizeECC-1:0]     ic_tag_rdata_o [IC_NUM_WAYS];
logic [IC_NUM_WAYS-1:0]    ic_data_req;
logic [IC_NUM_WAYS-1:0]    ic_data_gnt;
logic [IC_NUM_WAYS-1:0]    ic_data_rvalid;
logic                      ic_data_write;
logic [IC_INDEX_W-1:0]     ic_data_addr;
logic [LineSizeECC-1:0]    ic_data_wdata;
logic [LineSizeECC-1:0]    ic_data_rdata_in [IC_NUM_WAYS];
logic [LineSizeECC-1:0]    ic_data_rdata_o [IC_NUM_WAYS];
bit                        ecc_err;
bit   [TagSizeECC-1:0]     ic_tag_rdata_err [IC_NUM_WAYS];
bit   [LineSizeECC-1:0]    ic_data_rdata_err [IC_NUM_WAYS];
bit                        enable_ecc_errors;
bit   [IC_NUM_WAYS-1 : 0]  data_sel_line;
bit   [IC_NUM_WAYS-1 : 0]  tag_sel_line;
int   unsigned             dis_err_pct = 99;

clocking monitor_cb @(posedge clk);
  input  ic_tag_addr;
  input  ic_tag_write;
  input  ic_tag_req;
  input  ic_tag_wdata;
  input  ic_tag_rvalid;
  input  ic_tag_rdata_in;
  output ic_tag_rdata_o;
  input  ic_data_req;
  input  ic_data_gnt;
  input  ic_data_rvalid;
  input  ic_data_write;
  input  ic_data_addr;
  input  ic_data_wdata;
  input  ic_data_rdata_in;
  output ic_data_rdata_o;
  input  ecc_err;
  input  enable_ecc_errors;
endclocking

for(genvar i = 0; i < IC_NUM_WAYS; i++) begin : g_assign_vals
  assign ic_data_rdata_o[i] = (enable_ecc_errors && ic_data_rvalid[i]) ?
                              ic_data_rdata_err[i] : ic_data_rdata_in[i];
  assign ic_tag_rdata_o[i]  = (enable_ecc_errors && ic_tag_rvalid[i]) ?
                              ic_tag_rdata_err[i]  : ic_tag_rdata_in[i];
end

function automatic gen_tag_err();
  bit   [TagSizeECC-1:0]     tag_mask;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tag_sel_line, tag_sel_line dist {'b0 :/ dis_err_pct,
                                      [1:$] :/ 100 - dis_err_pct};, ,"ibex_icache_ram_if")
  for (int i = 0; i < IC_NUM_WAYS; i++) begin
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tag_mask, $countones(tag_mask) inside {[1:2]};, ,
                                       "ibex_icache_ram_if")
    ic_tag_rdata_err[i] = tag_sel_line[i] ? ic_tag_rdata_in[i] ^ tag_mask : ic_tag_rdata_in[i];
  end
endfunction

function automatic gen_data_err();
  bit   [LineSizeECC-1:0]    data_mask;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_sel_line, data_sel_line dist {'b0 :/ dis_err_pct,
                                     [1:$] :/ 100 - dis_err_pct};, ,"ibex_icache_ram_if")
  for (int i = 0; i < IC_NUM_WAYS; i++) begin
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_mask, $countones(data_mask) inside {[1:2]};, ,
                                       "ibex_icache_ram_if")
    ic_data_rdata_err[i] = data_sel_line[i] ? ic_data_rdata_in[i] ^ data_mask : ic_data_rdata_in[i];
  end
endfunction

always @(negedge clk) begin
  if (enable_ecc_errors && rst_n && (& ic_tag_rvalid)) begin
    gen_tag_err();
  end
end

always @(negedge clk) begin
  if (enable_ecc_errors && rst_n && (& ic_data_rvalid)) begin
    gen_data_err();
  end
end

`ASSERT(TagErrChk_A, (& ic_tag_rvalid) && enable_ecc_errors && (tag_sel_line != 0) |-> ecc_err,
        clk, rst_n)

for (genvar i = 0; i < IC_NUM_WAYS; i++) begin : g_data_assertion
  `ASSERT(DataErrChk_A,
          (& ic_data_rvalid) && !$isunknown(ic_data_rdata_in[i]) && (data_sel_line[i]) &&
          enable_ecc_errors |-> ecc_err,
          clk,
          rst_n)
end

`ASSERT(TagValidChk_A, always (& ic_tag_rvalid == (| ic_tag_rvalid)), clk, rst_n)
`ASSERT(DataValidChk_A, always (| ic_data_rvalid) == (& ic_data_rvalid), clk, rst_n)
endinterface
