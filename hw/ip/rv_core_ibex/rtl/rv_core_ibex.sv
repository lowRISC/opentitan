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
  parameter bit                 PMPEnable         = 1'b0,
  parameter int unsigned        PMPGranularity    = 0,
  parameter int unsigned        PMPNumRegions     = 4,
  parameter int unsigned        MHPMCounterNum    = 10,
  parameter int unsigned        MHPMCounterWidth  = 32,
  parameter bit                 RV32E             = 0,
  parameter ibex_pkg::rv32m_e   RV32M             = ibex_pkg::RV32MSingleCycle,
  parameter ibex_pkg::rv32b_e   RV32B             = ibex_pkg::RV32BNone,
  parameter ibex_pkg::regfile_e RegFile           = ibex_pkg::RegFileFF,
  parameter bit                 BranchTargetALU   = 1'b1,
  parameter bit                 WritebackStage    = 1'b1,
  parameter bit                 ICache            = 1'b0,
  parameter bit                 ICacheECC         = 1'b0,
  parameter bit                 BranchPredictor   = 1'b0,
  parameter bit                 DbgTriggerEn      = 1'b1,
  parameter bit                 SecureIbex        = 1'b0,
  parameter int unsigned        DmHaltAddr        = 32'h1A110800,
  parameter int unsigned        DmExceptionAddr   = 32'h1A110808,
  parameter bit                 PipeLine          = 1'b0
) (
  // Clock and Reset
  input  logic        clk_i,
  input  logic        rst_ni,
  // Clock domain for escalation receiver
  input  logic        clk_esc_i,
  input  logic        rst_esc_ni,

  input  logic        test_en_i,     // enable all clock gates for testing
  input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

  input  logic [31:0] hart_id_i,
  input  logic [31:0] boot_addr_i,

  // Instruction memory interface
  output tlul_pkg::tl_h2d_t     tl_i_o,
  input  tlul_pkg::tl_d2h_t     tl_i_i,

  // Data memory interface
  output tlul_pkg::tl_h2d_t     tl_d_o,
  input  tlul_pkg::tl_d2h_t     tl_d_i,

  // Interrupt inputs
  input  logic        irq_software_i,
  input  logic        irq_timer_i,
  input  logic        irq_external_i,

  // Escalation input for NMI
  input  prim_esc_pkg::esc_tx_t esc_tx_i,
  output prim_esc_pkg::esc_rx_t esc_rx_o,

  // Debug Interface
  input  logic        debug_req_i,

  // Crash dump information
  output ibex_pkg::crash_dump_t crash_dump_o,

  // CPU Control Signals
  input lc_ctrl_pkg::lc_tx_t lc_cpu_en_i,
  output logic        core_sleep_o
);

  import top_pkg::*;
  import tlul_pkg::*;

  // if pipeline=1, do not allow pass through and always break the path
  // if pipeline is 0, passthrough the fifo completely
  localparam bit FifoPass = PipeLine ? 1'b0 : 1'b1;
  localparam int unsigned FifoDepth = PipeLine ? 2 : 0;
  // ICache creates more outstanding transactions
  localparam int NumOutstandingReqs = ICache ? 8 : 2;

  // Instruction interface (internal)
  logic        instr_req;
  logic        instr_gnt;
  logic        instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;
  logic        instr_err;

  // Data interface (internal)
  logic        data_req;
  logic        data_gnt;
  logic        data_rvalid;
  logic        data_we;
  logic [3:0]  data_be;
  logic [31:0] data_addr;
  logic [31:0] data_wdata;
  logic [31:0] data_rdata;
  logic        data_err;

  // Pipeline interfaces
  tl_h2d_t tl_i_ibex2fifo;
  tl_d2h_t tl_i_fifo2ibex;
  tl_h2d_t tl_d_ibex2fifo;
  tl_d2h_t tl_d_fifo2ibex;

  // Intermediate TL signals to connect an sram used in simulations.
  tlul_pkg::tl_h2d_t tl_d_o_int;
  tlul_pkg::tl_d2h_t tl_d_i_int;


`ifdef RVFI
  logic        rvfi_valid;
  logic [63:0] rvfi_order;
  logic [31:0] rvfi_insn;
  logic        rvfi_trap;
  logic        rvfi_halt;
  logic        rvfi_intr;
  logic [ 1:0] rvfi_mode;
  logic [ 1:0] rvfi_ixl;
  logic [ 4:0] rvfi_rs1_addr;
  logic [ 4:0] rvfi_rs2_addr;
  logic [ 4:0] rvfi_rs3_addr;
  logic [31:0] rvfi_rs1_rdata;
  logic [31:0] rvfi_rs2_rdata;
  logic [31:0] rvfi_rs3_rdata;
  logic [ 4:0] rvfi_rd_addr;
  logic [31:0] rvfi_rd_wdata;
  logic [31:0] rvfi_pc_rdata;
  logic [31:0] rvfi_pc_wdata;
  logic [31:0] rvfi_mem_addr;
  logic [ 3:0] rvfi_mem_rmask;
  logic [ 3:0] rvfi_mem_wmask;
  logic [31:0] rvfi_mem_rdata;
  logic [31:0] rvfi_mem_wdata;
`endif

  // Escalation receiver that converts differential
  // protocol into single ended signal.
  logic esc_irq_nm;
  prim_esc_receiver u_prim_esc_receiver (
    .clk_i    ( clk_esc_i  ),
    .rst_ni   ( rst_esc_ni ),
    .esc_en_o ( esc_irq_nm ),
    .esc_rx_o,
    .esc_tx_i
  );

  // Synchronize to fast Ibex clock domain.
  logic irq_nm;
  prim_flop_2sync #(
    .Width(1)
  ) u_prim_flop_2sync (
    .clk_i,
    .rst_ni,
    .d_i(esc_irq_nm),
    .q_o(irq_nm)
  );

  // Alert outputs
  // TODO - Wire these up once driven
  logic alert_minor, alert_major;
  logic unused_alert_minor, unused_alert_major;
  assign unused_alert_minor = alert_minor;
  assign unused_alert_major = alert_major;

  lc_ctrl_pkg::lc_tx_t [0:0] lc_cpu_en;
  prim_lc_sync u_lc_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_cpu_en_i),
    .lc_en_o(lc_cpu_en)
  );

  ibex_core #(
    .PMPEnable                ( PMPEnable                ),
    .PMPGranularity           ( PMPGranularity           ),
    .PMPNumRegions            ( PMPNumRegions            ),
    .MHPMCounterNum           ( MHPMCounterNum           ),
    .MHPMCounterWidth         ( MHPMCounterWidth         ),
    .RV32E                    ( RV32E                    ),
    .RV32M                    ( RV32M                    ),
    .RV32B                    ( RV32B                    ),
    .RegFile                  ( RegFile                  ),
    .BranchTargetALU          ( BranchTargetALU          ),
    .WritebackStage           ( WritebackStage           ),
    .ICache                   ( ICache                   ),
    .ICacheECC                ( ICacheECC                ),
    .BranchPredictor          ( BranchPredictor          ),
    .DbgTriggerEn             ( DbgTriggerEn             ),
    .SecureIbex               ( SecureIbex               ),
    .DmHaltAddr               ( DmHaltAddr               ),
    .DmExceptionAddr          ( DmExceptionAddr          )
  ) u_core (
    .clk_i,
    .rst_ni,

    .test_en_i,
    .ram_cfg_i,

    .hart_id_i,
    .boot_addr_i,

    .instr_req_o    ( instr_req    ),
    .instr_gnt_i    ( instr_gnt    ),
    .instr_rvalid_i ( instr_rvalid ),
    .instr_addr_o   ( instr_addr   ),
    .instr_rdata_i  ( instr_rdata  ),
    .instr_err_i    ( instr_err    ),

    .data_req_o     ( data_req     ),
    .data_gnt_i     ( data_gnt     ),
    .data_rvalid_i  ( data_rvalid  ),
    .data_we_o      ( data_we      ),
    .data_be_o      ( data_be      ),
    .data_addr_o    ( data_addr    ),
    .data_wdata_o   ( data_wdata   ),
    .data_rdata_i   ( data_rdata   ),
    .data_err_i     ( data_err     ),

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i     ( '0           ),
    .irq_nm_i       ( irq_nm       ),

    .debug_req_i,
    .crash_dump_o,

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

    .fetch_enable_i   (lc_cpu_en[0] == lc_ctrl_pkg::On),
    .alert_minor_o    (alert_minor),
    .alert_major_o    (alert_major),
    .core_sleep_o
  );

  //
  // Convert ibex data/instruction bus to TL-UL
  //

  tlul_adapter_host #(
    .MAX_REQS(NumOutstandingReqs)
  ) tl_adapter_host_i_ibex (
    .clk_i,
    .rst_ni,
    .req_i      (instr_req),
    .type_i     (tlul_pkg::InstrType),
    .gnt_o      (instr_gnt),
    .addr_i     (instr_addr),
    .we_i       (1'b0),
    .wdata_i    (32'b0),
    .be_i       (4'hF),
    .valid_o    (instr_rvalid),
    .rdata_o    (instr_rdata),
    .err_o      (instr_err),
    .intg_err_o (),
    .tl_o       (tl_i_ibex2fifo),
    .tl_i       (tl_i_fifo2ibex)
  );

  tlul_fifo_sync #(
    .ReqPass(FifoPass),
    .RspPass(FifoPass),
    .ReqDepth(FifoDepth),
    .RspDepth(FifoDepth)
  ) fifo_i (
    .clk_i,
    .rst_ni,
    .tl_h_i      (tl_i_ibex2fifo),
    .tl_h_o      (tl_i_fifo2ibex),
    .tl_d_o      (tl_i_o),
    .tl_d_i      (tl_i_i),
    .spare_req_i (1'b0),
    .spare_req_o (),
    .spare_rsp_i (1'b0),
    .spare_rsp_o ());

  tlul_adapter_host #(
    .MAX_REQS(2)
  ) tl_adapter_host_d_ibex (
    .clk_i,
    .rst_ni,
    .req_i      (data_req),
    .type_i     (tlul_pkg::DataType),
    .gnt_o      (data_gnt),
    .addr_i     (data_addr),
    .we_i       (data_we),
    .wdata_i    (data_wdata),
    .be_i       (data_be),
    .valid_o    (data_rvalid),
    .rdata_o    (data_rdata),
    .err_o      (data_err),
    .intg_err_o (),
    .tl_o       (tl_d_ibex2fifo),
    .tl_i       (tl_d_fifo2ibex)
  );

  tlul_fifo_sync #(
    .ReqPass(FifoPass),
    .RspPass(FifoPass),
    .ReqDepth(FifoDepth),
    .RspDepth(FifoDepth)
  ) fifo_d (
    .clk_i,
    .rst_ni,
    .tl_h_i      (tl_d_ibex2fifo),
    .tl_h_o      (tl_d_fifo2ibex),
    .tl_d_o      (tl_d_o_int),
    .tl_d_i      (tl_d_i_int),
    .spare_req_i (1'b0),
    .spare_req_o (),
    .spare_rsp_i (1'b0),
    .spare_rsp_o ());

  //
  // Interception point for connecting simulation SRAM by disconnecting the tl_d output. The
  // disconnection is done only if `SYNTHESIS is NOT defined AND `RV_CORE_IBEX_SIM_SRAM is
  // defined.
  //
`ifdef RV_CORE_IBEX_SIM_SRAM
`ifdef SYNTHESIS
  // Induce a compilation error by instantiating a non-existent module.
  illegal_preprocessor_branch_taken u_illegal_preprocessor_branch_taken();
`endif
`else
  assign tl_d_o = tl_d_o_int;
  assign tl_d_i_int = tl_d_i;
`endif

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
