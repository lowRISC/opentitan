// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
This is the top module. Everything else in the "check" directory is included in this file.
This module contains the ibex instance, the specification instance and the assertions
(included via the built psgen file), most of the non assertion code is setting up
infrastructure for those assertions.

It has the same ports as the ibex top.
*/

// Preprocessor decoding of instructions. Could be replaced with internal signals of the Sail one day
`include "encodings.sv"
// Abstract memory interface definition.
`include "protocol/mem.sv"

`define CR ibex_top_i.u_ibex_core
`define CSR `CR.cs_registers_i
`define CSRG `CSR.gen_scr
`define CSRP `CSR.g_pmp_registers
`define LSU `CR.load_store_unit_i
`define ID `CR.id_stage_i
`define IDG `ID.gen_stall_mem
`define IDC `ID.controller_i
`define WB `CR.wb_stage_i
`define WBG `WB.g_writeback_stage
`define RF ibex_top_i.gen_regfile_ff.register_file_i
`define IF `CR.if_stage_i
`define IFP `IF.gen_prefetch_buffer.prefetch_buffer_i
`define MULT `CR.ex_block_i.gen_multdiv_fast.multdiv_i
`define MULTG `MULT.gen_mult_fast

module top import ibex_pkg::*; #(
  parameter int unsigned DmHaltAddr       = 32'h1A110800,
  parameter int unsigned DmExceptionAddr  = 32'h1A110808,
  parameter bit          SecureIbex       = 1'b0,
  parameter bit          WritebackStage   = 1'b1,
  parameter bit          RV32E            = 1'b0,
  parameter rv32zc_e     RV32ZC           = RV32Zca,
  parameter int unsigned PMPNumRegions    = 4
) (
  // Clock and Reset
  input  logic                                                         clk_i,

  `ifndef YOSYS
  input  logic                                                         rst_ni,
  `endif

  input  logic                                                         test_en_i,
  input  prim_ram_1p_pkg::ram_1p_cfg_t                                 ram_cfg_icache_tag_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ibex_pkg::IC_NUM_WAYS-1:0] ram_cfg_rsp_icache_tag_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_t                                 ram_cfg_icache_data_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ibex_pkg::IC_NUM_WAYS-1:0] ram_cfg_rsp_icache_data_o,

  input  logic [31:0]                                                  hart_id_i,
  input  logic [31:0]                                                  boot_addr_i,

  // Instruction memory interface
  output logic                                                         instr_req_o,
  input  logic                                                         instr_gnt_i,
  input  logic                                                         instr_rvalid_i,
  output logic [31:0]                                                  instr_addr_o,
  input  logic [31:0]                                                  instr_rdata_i,
  input  logic [6:0]                                                   instr_rdata_intg_i,
  input  logic                                                         instr_err_i,

  // Data memory interface
  output logic                                                         data_req_o,
  output logic                                                         data_is_cap_o,
  input  logic                                                         data_gnt_i,
  input  logic                                                         data_rvalid_i,
  output logic                                                         data_we_o,
  output logic [3:0]                                                   data_be_o,
  output logic [31:0]                                                  data_addr_o,
  output logic [31:0]                                                  data_wdata_o,
  output logic [6:0]                                                   data_wdata_intg_o,
  input  logic [31:0]                                                  data_rdata_i,
  input  logic [6:0]                                                   data_rdata_intg_i,
  input  logic                                                         data_err_i,

  // Interrupt inputs
  input  logic                                                         irq_software_i,
  input  logic                                                         irq_timer_i,
  input  logic                                                         irq_external_i,
  input  logic [14:0]                                                  irq_fast_i,
  // non-maskable interrupt
  input  logic                                                         irq_nm_i,

  // Scrambling Interface
  input  logic                                                         scramble_key_valid_i,
  input  logic [SCRAMBLE_KEY_W-1:0]                                    scramble_key_i,
  input  logic [SCRAMBLE_NONCE_W-1:0]                                  scramble_nonce_i,
  output logic                                                         scramble_req_o,

  // Debug Interface
  input  logic                                                         debug_req_i,
  output crash_dump_t                                                  crash_dump_o,
  output logic                                                         double_fault_seen_o,

  // CPU Control Signals
  input  ibex_mubi_t                                                   fetch_enable_i,
  output logic                                                         core_sleep_o,
  output logic                                                         alert_minor_o,
  output logic                                                         alert_major_internal_o,
  output logic                                                         alert_major_bus_o,


  // DFT bypass controls
  input logic                                                          scan_rst_ni,

  // Lockstep signals
  output ibex_mubi_t                                                  lockstep_cmp_en_o,

  // Shadow core data interface outputs
  output logic                                                        data_req_shadow_o,
  output logic                                                        data_we_shadow_o,
  output logic [3:0]                                                  data_be_shadow_o,
  output logic [31:0]                                                 data_addr_shadow_o,
  output logic [31:0]                                                 data_wdata_shadow_o,
  output logic [6:0]                                                  data_wdata_intg_shadow_o,

  // Shadow core instruction interface outputs
  output logic                                                        instr_req_shadow_o,
  output logic [31:0]                                                 instr_addr_shadow_o
);

// Yosys based tools have no inherent understanding of a reset signal (unlike jasper, which has the
// `reset` TCL command). We must therefore introduce one ourselves using an initial block.
`ifdef YOSYS
logic rst_ni;
initial rst_ni = 1'b0;
always @(posedge clk_i) rst_ni = 1'b1;
`endif

localparam logic [31:0] CSR_MVENDORID_VALUE = 32'b0;
localparam logic [31:0] CSR_MIMPID_VALUE = 32'b0;

default clocking @(posedge clk_i); endclocking

ibex_top #(
    .DmHaltAddr(DmHaltAddr),
    .DmExceptionAddr(DmExceptionAddr),
    .SecureIbex(SecureIbex),
    .WritebackStage(WritebackStage),
    .RV32E(RV32E),
    .RV32ZC(RV32ZC),
    .BranchTargetALU(1'b1),
    .PMPEnable(1'b1),
    .PMPNumRegions(PMPNumRegions),
    .CsrMvendorId (CSR_MVENDORID_VALUE),
    .CsrMimpId (CSR_MIMPID_VALUE)
) ibex_top_i(.*);

// Core constraints
// 1. We do not allow going into debug mode
NotDebug: assume property (!ibex_top_i.u_ibex_core.debug_mode & !debug_req_i);
// 2. The boot address is constant
ConstantBoot: assume property (boot_addr_i == $past(boot_addr_i));
// 3. Always fetch enable
FetchEnable: assume property (fetch_enable_i == IbexMuBiOn);
// 4. Never try to sleep if we couldn't ever wake up
WFIStart: assume property (`IDC.ctrl_fsm_cs == SLEEP |-> (
                                                          `CSR.mie_q.irq_software |
                                                          `CSR.mie_q.irq_timer |
                                                          `CSR.mie_q.irq_external
                                                         ));
// See protocol/* for further assumptions

///////////////////////////////// Declarations /////////////////////////////////

// Helpful macros to define each relevant, checked CSR and their types.
// Some CSRs are not checked or tracked, see ex_is_checkable_csr below.
`define X_EACH_CSR \
    `ifndef X_DISABLE_PC `X(pc) `endif \
    `X(priv) \
    `X(mstatus) \
    `X(mie) \
    `X(mcause) \
    `X(mtval) \
    `X(mtvec) \
    `X(mscratch) \
    `X(mepc) \
    `X(mcounteren) \
    `X(pmp_cfg) \
    `X(pmp_addr) \
    `X(mseccfg)

`define X_EACH_CSR_TYPED \
    logic [31:0] `X(pc); \
    t_Privilege `X(priv); \
    mstatus_t `X(mstatus); \
    logic [31:0] `X(mie); \
    logic [31:0] `X(mcause); \
    logic [31:0] `X(mtval); \
    logic [31:0] `X(mtvec); \
    logic [31:0] `X(mscratch); \
    logic [31:0] `X(mepc); \
    logic [63:0] `X(mcycle); \
    logic [31:0] `X(mshwmb); \
    logic [31:0] `X(mshwm); \
    logic [31:0] `X(mcounteren); \
    logic [7:0] `X(pmp_cfg)[PMPNumRegions]; \
    logic [31:0] `X(pmp_addr)[PMPNumRegions]; \
    logic [31:0] `X(mseccfg);

////////////////////// Abstract State //////////////////////

// Pre state is the architectural state of Ibex at the start of the cycle
logic [31:0] pre_regs[32];
logic [31:0] pre_regs_cut[1:31];
logic [31:0] pre_nextpc;
logic [31:0] pre_mip;

`define X(n) pre_``n
`X_EACH_CSR_TYPED
`undef X

// Post state is the architectural state of Ibex at the end of this cycle, or the start of the next
`define X(n) post_``n
`X_EACH_CSR_TYPED
`undef X

////////////////////// Following //////////////////////
// Generally:
//  - ex_P is 1 if P is true for the instruction in the ID/EX stage.
//  - wbexc_P is 1 if P is true for the instruction in the WB/EXC (exception) stage.

logic ex_is_wfi, ex_is_rtype, ex_is_div, ex_is_mtype;
logic ex_is_btype, ex_is_jump;
logic ex_is_mem_instr, ex_is_load_instr, ex_is_store_instr;

// Have we branched, or are we branching in this cycle?
logic ex_has_branched_d, ex_has_branched_q;
logic [31:0] ex_branch_dst;
assign ex_branch_dst = `CR.branch_decision ? `CR.branch_target_ex : pre_nextpc;

logic outstanding_mem;
assign outstanding_mem = `ID.outstanding_load_wb_i || `ID.outstanding_store_wb_i;

logic has_resp_waiting_q, has_resp_waiting_d;
assign has_resp_waiting_q = data_mem_assume.outstanding_reqs_q != 8'h0;
assign has_resp_waiting_d = data_mem_assume.outstanding_reqs != 8'h0;

logic has_one_resp_waiting_q, has_one_resp_waiting_d;
assign has_one_resp_waiting_q = data_mem_assume.outstanding_reqs_q == 8'h1;
assign has_one_resp_waiting_d = data_mem_assume.outstanding_reqs == 8'h1;

logic has_two_resp_waiting_q, has_two_resp_waiting_d;
assign has_two_resp_waiting_q = data_mem_assume.outstanding_reqs_q == 8'h2;
assign has_two_resp_waiting_d = data_mem_assume.outstanding_reqs == 8'h2;

logic wbexc_is_load_instr, wbexc_is_store_instr, wbexc_is_mem_instr;
logic wbexc_is_wfi;

logic [31:0] ex_compressed_instr;
logic ex_has_compressed_instr;

// Stored specification post state
logic wbexc_post_int_err; // Spec had an internal error

logic [31:0] wbexc_post_wX;
logic [4:0] wbexc_post_wX_addr;
logic wbexc_post_wX_en;

`define X(n) wbexc_post_``n
`X_EACH_CSR_TYPED
`undef X

// Stored predetermined memory responses, see check/peek/mem.sv
logic [31:0] wbexc_spec_mem_read_fst_rdata;
logic [31:0] wbexc_spec_mem_read_snd_rdata;

// Store DUT CSR post state
`define X(n) wbexc_dut_post_``n
`X_EACH_CSR_TYPED
`undef X

logic [31:0] wbexc_instr; // original potentially compressed
logic [31:0] wbexc_decompressed_instr; // post decompression
logic wbexc_is_compressed;

logic [31:0] wbexc_pc;

logic mem_gnt_fst_d; // We are having or have had the first gnt
logic mem_gnt_fst_q; // We have had the first gnt before now
logic mem_gnt_snd_d; // We are having or have had the second gnt
logic mem_gnt_snd_q; // We have had the second gnt before now

logic mem_req_fst_d; // We are having the first req
logic mem_req_snd_d; // We are having the second req

logic wbexc_mem_had_snd_req; // During ID/EX there was a second request

logic lsu_had_first_resp;
assign lsu_had_first_resp = `LSU.ls_fsm_cs == `LSU.WAIT_GNT && `LSU.split_misaligned_access;

////////////////////// Wrap signals //////////////////////

logic spec_en; // The specification is being queried in this cycle
logic has_spec_past; // There is a previous step to compare against.
                     // Will become 0 on uncheckable CSRs and at reset.

// The previous specification output to be compared with the new input
logic [31:0] spec_past_regs[32];
logic [31:0] spec_past_has_reg; // Registers will have past values only when they are written to.
`define X(n) spec_past_``n
`X_EACH_CSR_TYPED
`undef X

////////////////////// Pipeline signals //////////////////////

logic ex_success; // Execute stage succeeding
logic ex_err; // Execute stage erroring
logic ex_kill; // Execute stage killed
logic exc_finishing; // Exception finishing
logic wb_finishing; // WB finishing
logic wbexc_finishing; // WB/EXC finishing
logic wbexc_exists; // Instruction in WB/EXC
logic wbexc_ex_err; // EXC has an execute error
logic wbexc_fetch_err; // EXC has a fetch error
logic wbexc_illegal; // EXC has an illegal instruction
logic wbexc_compressed_illegal; // EXC has an illegal instruction
logic wbexc_err; // EXC has an error
logic instr_will_progress; // Instruction will finish EX
logic wfi_will_finish; // WFI instruction retire by flushing the pipeline,
                       // but that isn't an exception.
logic wbexc_csr_pipe_flush; // The pipeline is being flushed due to a CSR write
logic wbexc_handling_irq; // Check the results of handling an IRQ

////////////////////// CSR selection //////////////////////
// Decide whether to compare wbexc_post_* and wbexc_dut_post_* or to use live versions.

// WBEXC CSR dut post state
`define X(n) wbexc_dut_cmp_post_``n
`X_EACH_CSR_TYPED
`undef X

// WBEXC CSR spec post state
`define X(n) wbexc_spec_cmp_post_``n
`X_EACH_CSR_TYPED
`undef X

////////////////////// Spec Post //////////////////////

logic [31:0] spec_post_wX;
logic [4:0] spec_post_wX_addr;
logic spec_post_wX_en;

`define X(n) spec_post_``n
`X_EACH_CSR_TYPED
`undef X

logic spec_int_err;

logic spec_fetch_err; // The specification has experienced a fetch error,
                      // regardless of whether or not it was told to.

logic spec_mem_read;
logic spec_mem_read_snd;
logic [31:0] spec_mem_read_fst_addr;
logic [31:0] spec_mem_read_snd_addr;
logic [31:0] spec_mem_read_fst_rdata; // Undriven
logic [31:0] spec_mem_read_snd_rdata; // Undriven

logic spec_mem_write;
logic spec_mem_write_snd;
logic [31:0] spec_mem_write_fst_addr;
logic [31:0] spec_mem_write_snd_addr;
logic [31:0] spec_mem_write_fst_wdata;
logic [31:0] spec_mem_write_snd_wdata;
logic [3:0] spec_mem_write_fst_be;
logic [3:0] spec_mem_write_snd_be;

logic spec_mem_en;
logic spec_mem_en_snd;
logic [31:0] spec_mem_fst_addr;
logic [31:0] spec_mem_snd_addr;
logic spec_has_pmp_err;

assign spec_mem_en = spec_mem_read | spec_mem_write;
assign spec_mem_en_snd = spec_mem_read_snd | spec_mem_write_snd;
assign spec_mem_fst_addr = spec_mem_read ? spec_mem_read_fst_addr : spec_mem_write_fst_addr;
assign spec_mem_snd_addr = spec_mem_read ? spec_mem_read_snd_addr : spec_mem_write_snd_addr;
assign spec_has_pmp_err = ~spec_mem_en || (`LSU.split_misaligned_access && ~spec_mem_en_snd);

logic [31:0] fst_mask, snd_mask;
assign fst_mask = {
    {8{spec_mem_write_fst_be[3]}}, {8{spec_mem_write_fst_be[2]}},
    {8{spec_mem_write_fst_be[1]}}, {8{spec_mem_write_fst_be[0]}}
};
assign snd_mask = {
    {8{spec_mem_write_snd_be[3]}}, {8{spec_mem_write_snd_be[2]}},
    {8{spec_mem_write_snd_be[1]}}, {8{spec_mem_write_snd_be[0]}}
};

logic fst_mem_cmp; // Condition for the first outgoing request to be spec conformant
assign fst_mem_cmp = (spec_mem_write == data_we_o) && (spec_mem_read == ~data_we_o) &&
                     (data_addr_o == spec_mem_fst_addr) &&
                     (data_we_o ->
                        (data_wdata_o & fst_mask) == (spec_mem_write_fst_wdata & fst_mask));
logic snd_mem_cmp; // Condition for the second outgoing request to be spec conformant
assign snd_mem_cmp = (spec_mem_write_snd == data_we_o) && (spec_mem_read_snd == ~data_we_o) &&
                     (data_addr_o == spec_mem_snd_addr) &&
                     (data_we_o ->
                        (data_wdata_o & snd_mask) == (spec_mem_write_snd_wdata & snd_mask));

logic lsu_waiting_for_misal;
assign lsu_waiting_for_misal =
      ((`LSU.data_type_q == 2'b00) && (`LSU.rdata_offset_q != 2'b00)) ||
      ((`LSU.data_type_q == 2'b01) && (`LSU.rdata_offset_q == 2'b11));

logic addr_last_matches;
assign addr_last_matches = `ID.rf_rdata_a_fwd +
                           (ex_is_store_instr? `ID.imm_s_type : `ID.imm_i_type) ==
                           `LSU.addr_last_q;

logic addr_last_d_matches;
assign addr_last_d_matches = `ID.rf_rdata_a_fwd +
                             (ex_is_store_instr? `ID.imm_s_type : `ID.imm_i_type) ==
                             `LSU.addr_last_d;

////////////////////// Compare //////////////////////

logic addr_match; // Register write index match
logic data_match; // Register write data match
logic csrs_match;
logic ex_csrs_match;
logic csrs_match_non_exc;
logic ex_csrs_match_non_exc;
logic pc_match;
logic finishing_executed; // Finishing normal case

`define INSTR `CR.instr_rdata_id

logic wbexc_is_checkable_csr;
logic ex_is_checkable_csr;
assign ex_is_checkable_csr = ~(
  ((CSR_MHPMCOUNTER3H <= `CSR_ADDR) && (`CSR_ADDR <= CSR_MHPMCOUNTER31H)) |
  ((CSR_MHPMCOUNTER3 <= `CSR_ADDR) && (`CSR_ADDR <= CSR_MHPMCOUNTER31)) |
  ((CSR_MHPMEVENT3 <= `CSR_ADDR) && (`CSR_ADDR <= CSR_MHPMEVENT31)) |
  (`CSR_ADDR == CSR_CPUCTRLSTS) | (`CSR_ADDR == CSR_SECURESEED) |
  (`CSR_ADDR == CSR_MIE) |
  (`CSR_ADDR == CSR_MCYCLE) | (`CSR_ADDR == CSR_MCYCLEH) |

  // TODO:
  (`CSR_ADDR == CSR_MINSTRET) | (`CSR_ADDR == CSR_MINSTRETH) |
  (`CSR_ADDR == CSR_MCOUNTINHIBIT)
);

`undef INSTR

////////////////////// Decompression Invariant Defs //////////////////////
// These will be used to show that the decompressed instruction stored is in fact the decompressed version of the compressed instruction.

logic [31:0] decompressed_instr;
logic decompressed_instr_illegal;
ibex_compressed_decoder #(
    .RV32ZC(RV32ZC),
    .ResetAll(SecureIbex)
) decompression_assertion_decoder (
    .clk_i,
    .rst_ni,
    .valid_i(1'b1),
    .id_in_ready_i(1'b1),
    .instr_i(ex_compressed_instr),
    .instr_o(decompressed_instr),
    .is_compressed_o(),
    .gets_expanded_o(),
    .illegal_instr_o(decompressed_instr_illegal)
);

logic [31:0] decompressed_instr_2;
logic decompressed_instr_illegal_2;
ibex_compressed_decoder #(
    .RV32ZC(RV32ZC),
    .ResetAll(SecureIbex)
) decompression_assertion_decoder_2(
    .clk_i,
    .rst_ni,
    .valid_i(1'b1),
    .id_in_ready_i(1'b1),
    .instr_i(wbexc_instr),
    .instr_o(decompressed_instr_2),
    .is_compressed_o(wbexc_is_compressed),
    .gets_expanded_o(),
    .illegal_instr_o(decompressed_instr_illegal_2)
);

////////////////////// IRQ + Memory Protocols //////////////////////
`include "protocol/irqs.sv"

mem_assume_t instr_mem_assume(
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_o    (instr_req_o),
    .gnt_i    (instr_gnt_i),
    .rvalid_i (instr_rvalid_i),
    .err_i    (instr_err_i)
);
mem_assume_t data_mem_assume(
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .req_o    (data_req_o),
    .gnt_i    (data_gnt_i),
    .rvalid_i (data_rvalid_i),
    .err_i    (data_err_i)
);

////////////////////// Following //////////////////////
`include "peek/abs.sv" // Abstract state
`include "peek/mem.sv" // Memory tracking
`include "peek/follower.sv" // Pipeline follower
`include "spec_instance.sv" // Instantiate the specification

////////////////////// Proof helpers ///////////////////////
`include "peek/compare_helper.sv"

////////////////////// Proof //////////////////////
`define INSTR wbexc_decompressed_instr
`ifdef YOSYS
`include "../build/psgen-yosys.sv"
`else
`include "../build/psgen-jg.sv"
`endif
`undef INSTR

// Assign spec fetch error after instantiating the specification.
assign spec_fetch_err =
    (main_mode == MAIN_IFERR && spec_api_i.main_result == MAINRES_OK) ||
    spec_api_i.main_result == MAINRES_IFERR_1 || spec_api_i.main_result == MAINRES_IFERR_2;

endmodule
