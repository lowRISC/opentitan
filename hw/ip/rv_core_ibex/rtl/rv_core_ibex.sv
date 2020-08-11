// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Ibex RISC-V core
 *
 * 32 bit RISC-V core supporting the RV32I + optionally EMC instruction sets.
 * Instruction and data bus are 32 bit wide TileLink-UL (TL-UL).
 */
module rv_core_ibex #(
    parameter bit PMPEnable = 1'b0,
    parameter int unsigned PMPGranularity = 0,
    parameter int unsigned PMPNumRegions = 4,
    parameter int unsigned MHPMCounterNum = 8,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit RV32E = 0,
    parameter bit RV32M = 1,
    parameter bit BranchTargetALU = 1,
    parameter bit WritebackStage = 1,
    parameter MultiplierImplementation = "single-cycle",
    parameter bit ICache = 1'b0,
    parameter bit ICacheECC = 1'b0,
    parameter bit DbgTriggerEn = 1'b1,
    parameter bit SecureIbex = 1'b0,
    parameter int unsigned DmHaltAddr = 32'h1A110800,
    parameter int unsigned DmExceptionAddr = 32'h1A110808,
    parameter bit PipeLine = 0
) (
    // Clock and Reset
    input logic clk_i,
    input logic rst_ni,

    input logic test_en_i,  // enable all clock gates for testing

    input logic [31:0] hart_id_i,
    input logic [31:0] boot_addr_i,

    // Instruction memory interface
    output tlul_pkg::tl_h2d_t tl_i_o,
    input  tlul_pkg::tl_d2h_t tl_i_i,

    // Data memory interface
    output tlul_pkg::tl_h2d_t tl_d_o,
    input  tlul_pkg::tl_d2h_t tl_d_i,

    // Interrupt inputs
    input logic        irq_software_i,
    input logic        irq_timer_i,
    input logic        irq_external_i,
    input logic [14:0] irq_fast_i,
    input logic        irq_nm_i,

    // Debug Interface
    input logic debug_req_i,

    // CPU Control Signals
    input  logic fetch_enable_i,
    output logic core_sleep_o
);

  import top_pkg::*;
  import tlul_pkg::*;

  // if pipeline=1, do not allow pass through and always break the path
  // if pipeline is 0, passthrough the fifo completely
  localparam int FifoPass = PipeLine ? 1'b0 : 1'b1;
  localparam int FifoDepth = PipeLine ? 4'h2 : 4'h0;

  // Instruction interface (internal)
  logic instr_req;
  logic instr_gnt;
  logic instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;
  logic instr_err;

  // Data interface (internal)
  logic data_req;
  logic data_gnt;
  logic data_rvalid;
  logic data_we;
  logic [3:0] data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;
  logic [31:0] data_rdata;
  logic data_err;

  // Pipeline interfaces
  tl_h2d_t tl_i_ibex2fifo;
  tl_d2h_t tl_i_fifo2ibex;
  tl_h2d_t tl_d_ibex2fifo;
  tl_d2h_t tl_d_fifo2ibex;

`ifdef RVFI
  logic rvfi_valid;
  logic [63:0] rvfi_order;
  logic [31:0] rvfi_insn;
  logic rvfi_trap;
  logic rvfi_halt;
  logic rvfi_intr;
  logic [1:0] rvfi_mode;
  logic [1:0] rvfi_ixl;
  logic [4:0] rvfi_rs1_addr;
  logic [4:0] rvfi_rs2_addr;
  logic [4:0] rvfi_rs3_addr;
  logic [31:0] rvfi_rs1_rdata;
  logic [31:0] rvfi_rs2_rdata;
  logic [31:0] rvfi_rs3_rdata;
  logic [4:0] rvfi_rd_addr;
  logic [31:0] rvfi_rd_wdata;
  logic [31:0] rvfi_pc_rdata;
  logic [31:0] rvfi_pc_wdata;
  logic [31:0] rvfi_mem_addr;
  logic [3:0] rvfi_mem_rmask;
  logic [3:0] rvfi_mem_wmask;
  logic [31:0] rvfi_mem_rdata;
  logic [31:0] rvfi_mem_wdata;
`endif

  ibex_core #(
      .PMPEnable(PMPEnable),
      .PMPGranularity(PMPGranularity),
      .PMPNumRegions(PMPNumRegions),
      .MHPMCounterNum(MHPMCounterNum),
      .MHPMCounterWidth(MHPMCounterWidth),
      .RV32E(RV32E),
      .RV32M(RV32M),
      .BranchTargetALU(BranchTargetALU),
      .WritebackStage(WritebackStage),
      .MultiplierImplementation(MultiplierImplementation),
      .ICache(ICache),
      .ICacheECC(ICacheECC),
      .DbgTriggerEn(DbgTriggerEn),
      .SecureIbex(SecureIbex),
      .DmHaltAddr(DmHaltAddr),
      .DmExceptionAddr(DmExceptionAddr)
  ) u_core (
      .clk_i,
      .rst_ni,

      .test_en_i,

      .hart_id_i,
      .boot_addr_i,

      .instr_req_o   (instr_req),
      .instr_gnt_i   (instr_gnt),
      .instr_rvalid_i(instr_rvalid),
      .instr_addr_o  (instr_addr),
      .instr_rdata_i (instr_rdata),
      .instr_err_i   (instr_err),

      .data_req_o   (data_req),
      .data_gnt_i   (data_gnt),
      .data_rvalid_i(data_rvalid),
      .data_we_o    (data_we),
      .data_be_o    (data_be),
      .data_addr_o  (data_addr),
      .data_wdata_o (data_wdata),
      .data_rdata_i (data_rdata),
      .data_err_i   (data_err),

      .irq_software_i,
      .irq_timer_i,
      .irq_external_i,
      .irq_fast_i,
      .irq_nm_i,

      .debug_req_i,

`ifdef RVFI
      .rvfi_valid,
      .rvfi_order,
      .rvfi_insn,
      .rvfi_trap,
      .rvfi_halt,
      .rvfi_intr,
      .rvfi_mode,
      .rvfi_ixl,
      .rvfi_rs1_addr,
      .rvfi_rs2_addr,
      .rvfi_rs3_addr,
      .rvfi_rs1_rdata,
      .rvfi_rs2_rdata,
      .rvfi_rs3_rdata,
      .rvfi_rd_addr,
      .rvfi_rd_wdata,
      .rvfi_pc_rdata,
      .rvfi_pc_wdata,
      .rvfi_mem_addr,
      .rvfi_mem_rmask,
      .rvfi_mem_wmask,
      .rvfi_mem_rdata,
      .rvfi_mem_wdata,
`endif

      .fetch_enable_i,
      .core_sleep_o
  );

  //
  // Convert ibex data/instruction bus to TL-UL
  //

  tlul_adapter_host #(
      .MAX_REQS(2)
  ) tl_adapter_host_i_ibex (
      .clk_i,
      .rst_ni,
      .req_i  (instr_req),
      .gnt_o  (instr_gnt),
      .addr_i (instr_addr),
      .we_i   (1'b0),
      .wdata_i(32'b0),
      .be_i   (4'hF),
      .valid_o(instr_rvalid),
      .rdata_o(instr_rdata),
      .err_o  (instr_err),
      .tl_o   (tl_i_ibex2fifo),
      .tl_i   (tl_i_fifo2ibex)
  );

  tlul_fifo_sync #(
      .ReqPass(FifoPass),
      .RspPass(FifoPass),
      .ReqDepth(FifoDepth),
      .RspDepth(FifoDepth)
  ) fifo_i (
      .clk_i,
      .rst_ni,
      .tl_h_i     (tl_i_ibex2fifo),
      .tl_h_o     (tl_i_fifo2ibex),
      .tl_d_o     (tl_i_o),
      .tl_d_i     (tl_i_i),
      .spare_req_i(1'b0),
      .spare_req_o(),
      .spare_rsp_i(1'b0),
      .spare_rsp_o()
  );

  tlul_adapter_host #(
      .MAX_REQS(2)
  ) tl_adapter_host_d_ibex (
      .clk_i,
      .rst_ni,
      .req_i  (data_req),
      .gnt_o  (data_gnt),
      .addr_i (data_addr),
      .we_i   (data_we),
      .wdata_i(data_wdata),
      .be_i   (data_be),
      .valid_o(data_rvalid),
      .rdata_o(data_rdata),
      .err_o  (data_err),
      .tl_o   (tl_d_ibex2fifo),
      .tl_i   (tl_d_fifo2ibex)
  );

  tlul_fifo_sync #(
      .ReqPass(FifoPass),
      .RspPass(FifoPass),
      .ReqDepth(FifoDepth),
      .RspDepth(FifoDepth)
  ) fifo_d (
      .clk_i,
      .rst_ni,
      .tl_h_i     (tl_d_ibex2fifo),
      .tl_h_o     (tl_d_fifo2ibex),
      .tl_d_o     (tl_d_o),
      .tl_d_i     (tl_d_i),
      .spare_req_i(1'b0),
      .spare_req_o(),
      .spare_rsp_i(1'b0),
      .spare_rsp_o()
  );


`ifdef RVFI
  ibex_tracer ibex_tracer_i (
      .clk_i,
      .rst_ni,

      .hart_id_i,

      .rvfi_valid,
      .rvfi_order,
      .rvfi_insn,
      .rvfi_trap,
      .rvfi_halt,
      .rvfi_intr,
      .rvfi_mode,
      .rvfi_ixl,
      .rvfi_rs1_addr,
      .rvfi_rs2_addr,
      .rvfi_rs3_addr,
      .rvfi_rs1_rdata,
      .rvfi_rs2_rdata,
      .rvfi_rs3_rdata,
      .rvfi_rd_addr,
      .rvfi_rd_wdata,
      .rvfi_pc_rdata,
      .rvfi_pc_wdata,
      .rvfi_mem_addr,
      .rvfi_mem_rmask,
      .rvfi_mem_wmask,
      .rvfi_mem_rdata,
      .rvfi_mem_wdata
  );
`endif


endmodule
