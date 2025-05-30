// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
These are various signals used in assertions. A lot of it is just convenient instruction checks,
some of it is checking spec conformance.
*/

`define INSTR wbexc_decompressed_instr

assign wbexc_is_pres_load_instr = `ISS_LB | `ISS_LBU | `ISS_LH | `ISS_LHU | `ISS_LW;
assign wbexc_is_pres_store_instr = `ISS_SB | `ISS_SH | `ISS_SW;
assign wbexc_is_pres_mem_instr = wbexc_is_pres_load_instr | wbexc_is_pres_store_instr;

assign wbexc_is_load_instr = `IS_LB | `IS_LBU | `IS_LH | `IS_LHU | `IS_LW;
assign wbexc_is_store_instr = `IS_SB | `IS_SH | `IS_SW;

assign wbexc_is_mem_instr = `IS_LB | `IS_LBU | `IS_SB |
                            `IS_LH | `IS_LHU | `IS_SH |
                            `IS_LW | `IS_SW;
assign wbexc_is_wfi = `IS_WFI & ~wbexc_fetch_err;
`undef INSTR

`define INSTR `CR.instr_rdata_id
assign ex_is_load_instr = `IS_LB | `IS_LBU | `IS_LH | `IS_LHU | `IS_LW;
assign ex_is_store_instr = `IS_SB | `IS_SH | `IS_SW;
assign ex_is_mem_instr = ex_is_load_instr | ex_is_store_instr;

assign ex_is_pres_load_instr = `ISS_LB | `ISS_LBU | `ISS_LH | `ISS_LHU | `ISS_LW;
assign ex_is_pres_store_instr = `ISS_SB | `ISS_SH | `ISS_SW;
assign ex_is_pres_mem_instr = ex_is_pres_load_instr | ex_is_pres_store_instr;

assign ex_is_pres_btype = `ISS_BTYPE;
assign ex_is_pres_jump = `ISS_JAL | `ISS_JALR;
assign ex_is_wfi = `IS_WFI;
assign ex_is_rtype = `IS_ADD | `IS_SUB | `IS_SLL | `IS_SLT | `IS_SLTU | `IS_XOR | `IS_SRL | `IS_SRA | `IS_OR | `IS_AND;
assign ex_is_div = `IS_DIV | `IS_DIVU | `IS_REM | `IS_REMU;
`undef INSTR

// real_write checks that there is a write and the dest reg is not x0
logic dut_real_write, spec_real_write;
assign dut_real_write = `WB.rf_we_wb_o & (|`WB.rf_waddr_wb_o);
assign spec_real_write = wbexc_post_wX_en & (|wbexc_post_wX_addr);

assign addr_match = dut_real_write == spec_real_write &&
                    (spec_real_write -> `WB.rf_waddr_wb_o == wbexc_post_wX_addr);
assign data_match = (spec_real_write && dut_real_write) -> wbexc_post_wX == `WB.rf_wdata_wb_o;

assign finishing_executed = wbexc_finishing & ~wbexc_fetch_err;

/*
Select CSRs based on the current state of the follower, in particular:
- In most cases we compare the CSRs that were about to written at the end of ID/EX to the CSRs from the spec also
  from that time. It's unfortunate to do that now but not a huge hassle.
- In the case of an exception or WFI we compare the CSRs about to be written now with the CSRs from the spec at the end of ID/EX
- In the case of an IRQ we compare the the CSRs about to be written now with the CSRs from the spec now
*/

`define INSTR `CR.instr_rdata_id

logic use_curr_dut, use_curr_spec;
assign use_curr_dut = wbexc_err | wbexc_handling_irq;
assign use_curr_spec = wbexc_handling_irq;

`define X(c) assign wbexc_dut_cmp_post_``c = use_curr_dut ? post_``c : wbexc_dut_post_``c;
`X_EACH_CSR
`undef X

`define X(c) assign wbexc_spec_cmp_post_``c = use_curr_spec ? spec_post_``c : wbexc_post_``c;
`X_EACH_CSR
`undef X

`define X_DISABLE_PC
`define X(c) wbexc_dut_cmp_post_``c == wbexc_spec_cmp_post_``c &&
assign csrs_match = `X_EACH_CSR 1;
`undef X
`undef X_DISABLE_PC

assign pc_match = wbexc_dut_cmp_post_pc == wbexc_spec_cmp_post_pc;

`define X_DISABLE_PC
assign csrs_didnt_change =
`define X(c) pre_``c == wbexc_dut_post_``c &&
  `X_EACH_CSR
`undef X
   1;
`undef X_DISABLE_PC

`define X_DISABLE_PC
assign ex_csrs_match =
`define X(c) post_``c == spec_post_``c &&
  `X_EACH_CSR
`undef X
   1;
`undef X_DISABLE_PC

assign csrs_match_non_exc =
`define X(c) post_``c == wbexc_post_``c &&
  `X(mstatus.mprv)
  `X(mstatus.tw)
  `X(mie)
  `X(mtvec)
  `X(mscratch)
  `X(mcounteren)
  `X(pmp_cfg)
  `X(pmp_addr)
  `X(mseccfg)
`undef X
   1;

assign ex_csrs_match_non_exc =
`define X(c) post_``c == spec_post_``c &&
  `X(mstatus.mprv)
  `X(mstatus.tw)
  `X(mie)
  `X(mtvec)
  `X(mscratch)
  `X(mcounteren)
  `X(pmp_cfg)
  `X(pmp_addr)
  `X(mseccfg)
`undef X
   1;
