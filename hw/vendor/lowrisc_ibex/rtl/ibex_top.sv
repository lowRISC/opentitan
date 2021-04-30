// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

`include "prim_assert.sv"

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_top #(
    parameter bit                 PMPEnable        = 1'b0,
    parameter int unsigned        PMPGranularity   = 0,
    parameter int unsigned        PMPNumRegions    = 4,
    parameter int unsigned        MHPMCounterNum   = 0,
    parameter int unsigned        MHPMCounterWidth = 40,
    parameter bit                 RV32E            = 1'b0,
    parameter ibex_pkg::rv32m_e   RV32M            = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e   RV32B            = ibex_pkg::RV32BNone,
    parameter ibex_pkg::regfile_e RegFile          = ibex_pkg::RegFileFF,
    parameter bit                 BranchTargetALU  = 1'b0,
    parameter bit                 WritebackStage   = 1'b0,
    parameter bit                 ICache           = 1'b0,
    parameter bit                 ICacheECC        = 1'b0,
    parameter bit                 BranchPredictor  = 1'b0,
    parameter bit                 DbgTriggerEn     = 1'b0,
    parameter int unsigned        DbgHwBreakNum    = 1,
    parameter bit                 SecureIbex       = 1'b0,
    parameter int unsigned        DmHaltAddr       = 32'h1A110800,
    parameter int unsigned        DmExceptionAddr  = 32'h1A110808
) (
    // Clock and Reset
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic                         test_en_i,     // enable all clock gates for testing
    input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

    input  logic [31:0]                  hart_id_i,
    input  logic [31:0]                  boot_addr_i,

    // Instruction memory interface
    output logic                         instr_req_o,
    input  logic                         instr_gnt_i,
    input  logic                         instr_rvalid_i,
    output logic [31:0]                  instr_addr_o,
    input  logic [31:0]                  instr_rdata_i,
    input  logic                         instr_err_i,

    // Data memory interface
    output logic                         data_req_o,
    input  logic                         data_gnt_i,
    input  logic                         data_rvalid_i,
    output logic                         data_we_o,
    output logic [3:0]                   data_be_o,
    output logic [31:0]                  data_addr_o,
    output logic [31:0]                  data_wdata_o,
    input  logic [31:0]                  data_rdata_i,
    input  logic                         data_err_i,

    // Interrupt inputs
    input  logic                         irq_software_i,
    input  logic                         irq_timer_i,
    input  logic                         irq_external_i,
    input  logic [14:0]                  irq_fast_i,
    input  logic                         irq_nm_i,       // non-maskeable interrupt

    // Debug Interface
    input  logic                         debug_req_i,
    output ibex_pkg::crash_dump_t        crash_dump_o,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic                         rvfi_valid,
    output logic [63:0]                  rvfi_order,
    output logic [31:0]                  rvfi_insn,
    output logic                         rvfi_trap,
    output logic                         rvfi_halt,
    output logic                         rvfi_intr,
    output logic [ 1:0]                  rvfi_mode,
    output logic [ 1:0]                  rvfi_ixl,
    output logic [ 4:0]                  rvfi_rs1_addr,
    output logic [ 4:0]                  rvfi_rs2_addr,
    output logic [ 4:0]                  rvfi_rs3_addr,
    output logic [31:0]                  rvfi_rs1_rdata,
    output logic [31:0]                  rvfi_rs2_rdata,
    output logic [31:0]                  rvfi_rs3_rdata,
    output logic [ 4:0]                  rvfi_rd_addr,
    output logic [31:0]                  rvfi_rd_wdata,
    output logic [31:0]                  rvfi_pc_rdata,
    output logic [31:0]                  rvfi_pc_wdata,
    output logic [31:0]                  rvfi_mem_addr,
    output logic [ 3:0]                  rvfi_mem_rmask,
    output logic [ 3:0]                  rvfi_mem_wmask,
    output logic [31:0]                  rvfi_mem_rdata,
    output logic [31:0]                  rvfi_mem_wdata,
`endif

    // CPU Control Signals
    input  logic                         fetch_enable_i,
    output logic                         alert_minor_o,
    output logic                         alert_major_o,
    output logic                         core_sleep_o,

    // DFT bypass controls
    input logic                          scan_rst_ni
);

  import ibex_pkg::*;

  localparam bit          Lockstep          = SecureIbex;
  localparam bit          DummyInstructions = SecureIbex;
  localparam bit          RegFileECC        = SecureIbex;
  localparam int unsigned RegFileDataWidth  = RegFileECC ? 32 + 7 : 32;
  // Icache parameters
  localparam int unsigned BusSizeECC        = ICacheECC ? (BUS_SIZE + 7) : BUS_SIZE;
  localparam int unsigned LineSizeECC       = BusSizeECC * IC_LINE_BEATS;
  localparam int unsigned TagSizeECC        = ICacheECC ? (IC_TAG_SIZE + 6) : IC_TAG_SIZE;

  // Clock signals
  logic                        clk;
  logic                        core_busy_d, core_busy_q;
  logic                        fetch_enable_q;
  logic                        clock_en;
  logic                        irq_pending;
  // Core <-> Register file signals
  logic                        dummy_instr_id;
  logic [4:0]                  rf_raddr_a;
  logic [4:0]                  rf_raddr_b;
  logic [4:0]                  rf_waddr_wb;
  logic                        rf_we_wb;
  logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_a_ecc;
  logic [RegFileDataWidth-1:0] rf_rdata_b_ecc;
  // Core <-> RAMs signals
  logic [IC_NUM_WAYS-1:0]      ic_tag_req;
  logic                        ic_tag_write;
  logic [IC_INDEX_W-1:0]       ic_tag_addr;
  logic [TagSizeECC-1:0]       ic_tag_wdata;
  logic [TagSizeECC-1:0]       ic_tag_rdata [IC_NUM_WAYS];
  logic [IC_NUM_WAYS-1:0]      ic_data_req;
  logic                        ic_data_write;
  logic [IC_INDEX_W-1:0]       ic_data_addr;
  logic [LineSizeECC-1:0]      ic_data_wdata;
  logic [LineSizeECC-1:0]      ic_data_rdata [IC_NUM_WAYS];
  // Alert signals
  logic                        core_alert_major, core_alert_minor;
  logic                        lockstep_alert_major, lockstep_alert_minor;

  /////////////////////
  // Main clock gate //
  /////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_busy_q <= 1'b0;
    end else begin
      core_busy_q <= core_busy_d;
    end
  end

  // capture fetch_enable_i in fetch_enable_q, once for ever
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fetch_enable_q <= 1'b0;
    end else if (fetch_enable_i) begin
      fetch_enable_q <= 1'b1;
    end
  end

  assign clock_en     = fetch_enable_q & (core_busy_q | debug_req_i | irq_pending | irq_nm_i);
  assign core_sleep_o = ~clock_en;

  prim_clock_gating core_clock_gate_i (
      .clk_i     ( clk_i           ),
      .en_i      ( clock_en        ),
      .test_en_i ( test_en_i       ),
      .clk_o     ( clk             )
  );

  ////////////////////////
  // Core instantiation //
  ////////////////////////

  ibex_core #(
    .PMPEnable         ( PMPEnable         ),
    .PMPGranularity    ( PMPGranularity    ),
    .PMPNumRegions     ( PMPNumRegions     ),
    .MHPMCounterNum    ( MHPMCounterNum    ),
    .MHPMCounterWidth  ( MHPMCounterWidth  ),
    .RV32E             ( RV32E             ),
    .RV32M             ( RV32M             ),
    .RV32B             ( RV32B             ),
    .BranchTargetALU   ( BranchTargetALU   ),
    .ICache            ( ICache            ),
    .ICacheECC         ( ICacheECC         ),
    .BusSizeECC        ( BusSizeECC        ),
    .TagSizeECC        ( TagSizeECC        ),
    .LineSizeECC       ( LineSizeECC       ),
    .BranchPredictor   ( BranchPredictor   ),
    .DbgTriggerEn      ( DbgTriggerEn      ),
    .DbgHwBreakNum     ( DbgHwBreakNum     ),
    .WritebackStage    ( WritebackStage    ),
    .SecureIbex        ( SecureIbex        ),
    .DummyInstructions ( DummyInstructions ),
    .RegFileECC        ( RegFileECC        ),
    .RegFileDataWidth  ( RegFileDataWidth  ),
    .DmHaltAddr        ( DmHaltAddr        ),
    .DmExceptionAddr   ( DmExceptionAddr   )
  ) u_ibex_core (
    .clk_i (clk),
    .rst_ni,

    .hart_id_i,
    .boot_addr_i,

    .instr_req_o,
    .instr_gnt_i,
    .instr_rvalid_i,
    .instr_addr_o,
    .instr_rdata_i,
    .instr_err_i,

    .data_req_o,
    .data_gnt_i,
    .data_rvalid_i,
    .data_we_o,
    .data_be_o,
    .data_addr_o,
    .data_wdata_o,
    .data_rdata_i,
    .data_err_i,

    .dummy_instr_id_o  (dummy_instr_id),
    .rf_raddr_a_o      (rf_raddr_a),
    .rf_raddr_b_o      (rf_raddr_b),
    .rf_waddr_wb_o     (rf_waddr_wb),
    .rf_we_wb_o        (rf_we_wb),
    .rf_wdata_wb_ecc_o (rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i  (rf_rdata_a_ecc),
    .rf_rdata_b_ecc_i  (rf_rdata_b_ecc),

    .ic_tag_req_o      (ic_tag_req),
    .ic_tag_write_o    (ic_tag_write),
    .ic_tag_addr_o     (ic_tag_addr),
    .ic_tag_wdata_o    (ic_tag_wdata),
    .ic_tag_rdata_i    (ic_tag_rdata),
    .ic_data_req_o     (ic_data_req),
    .ic_data_write_o   (ic_data_write),
    .ic_data_addr_o    (ic_data_addr),
    .ic_data_wdata_o   (ic_data_wdata),
    .ic_data_rdata_i   (ic_data_rdata),

    .irq_software_i,
    .irq_timer_i,
    .irq_external_i,
    .irq_fast_i,
    .irq_nm_i,
    .irq_pending_o (irq_pending),

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

    .alert_minor_o (core_alert_minor),
    .alert_major_o (core_alert_major),
    .core_busy_o (core_busy_d)
  );

  /////////////////////////////////
  // Register file Instantiation //
  /////////////////////////////////

  if (RegFile == RegFileFF) begin : gen_regfile_ff
    ibex_register_file_ff #(
        .RV32E             ( RV32E             ),
        .DataWidth         ( RegFileDataWidth  ),
        .DummyInstructions ( DummyInstructions )
    ) register_file_i (
        .clk_i            ( clk             ),
        .rst_ni           ( rst_ni          ),

        .test_en_i        ( test_en_i       ),
        .dummy_instr_id_i ( dummy_instr_id  ),

        .raddr_a_i        ( rf_raddr_a      ),
        .rdata_a_o        ( rf_rdata_a_ecc  ),
        .raddr_b_i        ( rf_raddr_b      ),
        .rdata_b_o        ( rf_rdata_b_ecc  ),
        .waddr_a_i        ( rf_waddr_wb     ),
        .wdata_a_i        ( rf_wdata_wb_ecc ),
        .we_a_i           ( rf_we_wb        )
    );
  end else if (RegFile == RegFileFPGA) begin : gen_regfile_fpga
    ibex_register_file_fpga #(
        .RV32E             ( RV32E             ),
        .DataWidth         ( RegFileDataWidth  ),
        .DummyInstructions ( DummyInstructions )
    ) register_file_i (
        .clk_i            ( clk             ),
        .rst_ni           ( rst_ni          ),

        .test_en_i        ( test_en_i       ),
        .dummy_instr_id_i ( dummy_instr_id  ),

        .raddr_a_i        ( rf_raddr_a      ),
        .rdata_a_o        ( rf_rdata_a_ecc  ),
        .raddr_b_i        ( rf_raddr_b      ),
        .rdata_b_o        ( rf_rdata_b_ecc  ),
        .waddr_a_i        ( rf_waddr_wb     ),
        .wdata_a_i        ( rf_wdata_wb_ecc ),
        .we_a_i           ( rf_we_wb        )
    );
  end else if (RegFile == RegFileLatch) begin : gen_regfile_latch
    ibex_register_file_latch #(
        .RV32E             ( RV32E             ),
        .DataWidth         ( RegFileDataWidth  ),
        .DummyInstructions ( DummyInstructions )
    ) register_file_i (
        .clk_i            ( clk             ),
        .rst_ni           ( rst_ni          ),

        .test_en_i        ( test_en_i       ),
        .dummy_instr_id_i ( dummy_instr_id  ),

        .raddr_a_i        ( rf_raddr_a      ),
        .rdata_a_o        ( rf_rdata_a_ecc  ),
        .raddr_b_i        ( rf_raddr_b      ),
        .rdata_b_o        ( rf_rdata_b_ecc  ),
        .waddr_a_i        ( rf_waddr_wb     ),
        .wdata_a_i        ( rf_wdata_wb_ecc ),
        .we_a_i           ( rf_we_wb        )
    );
  end

  ////////////////////////
  // Rams Instantiation //
  ////////////////////////

  if (ICache) begin : gen_rams

    for (genvar way = 0; way < IC_NUM_WAYS; way++) begin : gen_rams_inner
      // Tag RAM instantiation
      prim_ram_1p #(
        .Width           (TagSizeECC),
        .Depth           (IC_NUM_LINES),
        .DataBitsPerMask (TagSizeECC)
      ) tag_bank (
        .clk_i    (clk_i),
        .req_i    (ic_tag_req[way]),
        .cfg_i    (ram_cfg_i),
        .write_i  (ic_tag_write),
        .wmask_i  ({TagSizeECC{1'b1}}),
        .addr_i   (ic_tag_addr),
        .wdata_i  (ic_tag_wdata),
        .rdata_o  (ic_tag_rdata[way])
      );
      // Data RAM instantiation
      prim_ram_1p #(
        .Width           (LineSizeECC),
        .Depth           (IC_NUM_LINES),
        .DataBitsPerMask (LineSizeECC)
      ) data_bank (
        .clk_i    (clk_i),
        .req_i    (ic_data_req[way]),
        .cfg_i    (ram_cfg_i),
        .write_i  (ic_data_write),
        .wmask_i  ({LineSizeECC{1'b1}}),
        .addr_i   (ic_data_addr),
        .wdata_i  (ic_data_wdata),
        .rdata_o  (ic_data_rdata[way])
      );
    end

  end else begin : gen_norams

    prim_ram_1p_pkg::ram_1p_cfg_t unused_ram_cfg;
    logic unused_ram_inputs;

    assign unused_ram_cfg    = ram_cfg_i;
    assign unused_ram_inputs = (|ic_tag_req) & ic_tag_write & (|ic_tag_addr) & (|ic_tag_wdata) &
                               (|ic_data_req) & ic_data_write & (|ic_data_addr) & (|ic_data_wdata);
    assign ic_tag_rdata      = '{default:'b0};
    assign ic_data_rdata     = '{default:'b0};

  end

  // Redundant lockstep core implementation
  if (Lockstep) begin : gen_lockstep
    // Note: certain synthesis tools like DC are very smart at optimizing away redundant logic.
    // Hence, we have to insert an optimization barrier at the IOs of the lockstep Ibex.
    // This is achieved by manually buffering each bit using prim_buf.
    // Our Xilinx and DC synthesis flows make sure that these buffers cannot be optimized away
    // using keep attributes (Vivado) and size_only constraints (DC).

    localparam int NumBufferBits = $bits({
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_i,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_o,
      data_rdata_i,
      data_err_i,
      dummy_instr_id,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      core_busy_d
    });

    logic [NumBufferBits-1:0] buf_in, buf_out;

    logic [31:0]                  hart_id_local;
    logic [31:0]                  boot_addr_local;

    logic                         instr_req_local;
    logic                         instr_gnt_local;
    logic                         instr_rvalid_local;
    logic [31:0]                  instr_addr_local;
    logic [31:0]                  instr_rdata_local;
    logic                         instr_err_local;

    logic                         data_req_local;
    logic                         data_gnt_local;
    logic                         data_rvalid_local;
    logic                         data_we_local;
    logic [3:0]                   data_be_local;
    logic [31:0]                  data_addr_local;
    logic [31:0]                  data_wdata_local;
    logic [31:0]                  data_rdata_local;
    logic                         data_err_local;

    logic                         dummy_instr_id_local;
    logic [4:0]                   rf_raddr_a_local;
    logic [4:0]                   rf_raddr_b_local;
    logic [4:0]                   rf_waddr_wb_local;
    logic                         rf_we_wb_local;
    logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_local;
    logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_local;

    logic [IC_NUM_WAYS-1:0]       ic_tag_req_local;
    logic                         ic_tag_write_local;
    logic [IC_INDEX_W-1:0]        ic_tag_addr_local;
    logic [TagSizeECC-1:0]        ic_tag_wdata_local;
    logic [IC_NUM_WAYS-1:0]       ic_data_req_local;
    logic                         ic_data_write_local;
    logic [IC_INDEX_W-1:0]        ic_data_addr_local;
    logic [LineSizeECC-1:0]       ic_data_wdata_local;

    logic                         irq_software_local;
    logic                         irq_timer_local;
    logic                         irq_external_local;
    logic [14:0]                  irq_fast_local;
    logic                         irq_nm_local;
    logic                         irq_pending_local;

    logic                         debug_req_local;
    crash_dump_t                  crash_dump_local;

    logic                         core_busy_local;

    assign buf_in = {
      hart_id_i,
      boot_addr_i,
      instr_req_o,
      instr_gnt_i,
      instr_rvalid_i,
      instr_addr_o,
      instr_rdata_i,
      instr_err_i,
      data_req_o,
      data_gnt_i,
      data_rvalid_i,
      data_we_o,
      data_be_o,
      data_addr_o,
      data_wdata_o,
      data_rdata_i,
      data_err_i,
      dummy_instr_id,
      rf_raddr_a,
      rf_raddr_b,
      rf_waddr_wb,
      rf_we_wb,
      rf_wdata_wb_ecc,
      rf_rdata_a_ecc,
      rf_rdata_b_ecc,
      ic_tag_req,
      ic_tag_write,
      ic_tag_addr,
      ic_tag_wdata,
      ic_data_req,
      ic_data_write,
      ic_data_addr,
      ic_data_wdata,
      irq_software_i,
      irq_timer_i,
      irq_external_i,
      irq_fast_i,
      irq_nm_i,
      irq_pending,
      debug_req_i,
      crash_dump_o,
      core_busy_d
    };

    assign {
      hart_id_local,
      boot_addr_local,
      instr_req_local,
      instr_gnt_local,
      instr_rvalid_local,
      instr_addr_local,
      instr_rdata_local,
      instr_err_local,
      data_req_local,
      data_gnt_local,
      data_rvalid_local,
      data_we_local,
      data_be_local,
      data_addr_local,
      data_wdata_local,
      data_rdata_local,
      data_err_local,
      dummy_instr_id_local,
      rf_raddr_a_local,
      rf_raddr_b_local,
      rf_waddr_wb_local,
      rf_we_wb_local,
      rf_wdata_wb_ecc_local,
      rf_rdata_a_ecc_local,
      rf_rdata_b_ecc_local,
      ic_tag_req_local,
      ic_tag_write_local,
      ic_tag_addr_local,
      ic_tag_wdata_local,
      ic_data_req_local,
      ic_data_write_local,
      ic_data_addr_local,
      ic_data_wdata_local,
      irq_software_local,
      irq_timer_local,
      irq_external_local,
      irq_fast_local,
      irq_nm_local,
      irq_pending_local,
      debug_req_local,
      crash_dump_local,
      core_busy_local
    } = buf_out;

    // Manually buffer all input signals.
    for (genvar k = 0; k < NumBufferBits; k++) begin : gen_buffers
      prim_buf u_prim_buf (
        .in_i(buf_in[k]),
        .out_o(buf_out[k])
      );
    end

    logic [TagSizeECC-1:0]  ic_tag_rdata_local [IC_NUM_WAYS];
    logic [LineSizeECC-1:0] ic_data_rdata_local [IC_NUM_WAYS];
    for (genvar k = 0; k < IC_NUM_WAYS; k++) begin : gen_ways
      for (genvar j = 0; j < TagSizeECC; j++) begin : gen_tag_bufs
        prim_buf u_prim_buf (
          .in_i(ic_tag_rdata[k][j]),
          .out_o(ic_tag_rdata_local[k][j])
        );
      end
      for (genvar j = 0; j < LineSizeECC; j++) begin : gen_data_bufs
        prim_buf u_prim_buf (
          .in_i(ic_data_rdata[k][j]),
          .out_o(ic_data_rdata_local[k][j])
        );
      end
    end

    logic lockstep_alert_minor_local, lockstep_alert_major_local;
    ibex_lockstep #(
      .PMPEnable         ( PMPEnable         ),
      .PMPGranularity    ( PMPGranularity    ),
      .PMPNumRegions     ( PMPNumRegions     ),
      .MHPMCounterNum    ( MHPMCounterNum    ),
      .MHPMCounterWidth  ( MHPMCounterWidth  ),
      .RV32E             ( RV32E             ),
      .RV32M             ( RV32M             ),
      .RV32B             ( RV32B             ),
      .BranchTargetALU   ( BranchTargetALU   ),
      .ICache            ( ICache            ),
      .ICacheECC         ( ICacheECC         ),
      .BusSizeECC        ( BusSizeECC        ),
      .TagSizeECC        ( TagSizeECC        ),
      .LineSizeECC       ( LineSizeECC       ),
      .BranchPredictor   ( BranchPredictor   ),
      .DbgTriggerEn      ( DbgTriggerEn      ),
      .DbgHwBreakNum     ( DbgHwBreakNum     ),
      .WritebackStage    ( WritebackStage    ),
      .SecureIbex        ( SecureIbex        ),
      .DummyInstructions ( DummyInstructions ),
      .RegFileECC        ( RegFileECC        ),
      .RegFileDataWidth  ( RegFileDataWidth  ),
      .DmHaltAddr        ( DmHaltAddr        ),
      .DmExceptionAddr   ( DmExceptionAddr   )
    ) u_ibex_lockstep (
      .clk_i             (clk),
      .rst_ni            (rst_ni),

      .hart_id_i         (hart_id_local),
      .boot_addr_i       (boot_addr_local),

      .instr_req_i       (instr_req_local),
      .instr_gnt_i       (instr_gnt_local),
      .instr_rvalid_i    (instr_rvalid_local),
      .instr_addr_i      (instr_addr_local),
      .instr_rdata_i     (instr_rdata_local),
      .instr_err_i       (instr_err_local),

      .data_req_i        (data_req_local),
      .data_gnt_i        (data_gnt_local),
      .data_rvalid_i     (data_rvalid_local),
      .data_we_i         (data_we_local),
      .data_be_i         (data_be_local),
      .data_addr_i       (data_addr_local),
      .data_wdata_i      (data_wdata_local),
      .data_rdata_i      (data_rdata_local),
      .data_err_i        (data_err_local),

      .dummy_instr_id_i  (dummy_instr_id_local),
      .rf_raddr_a_i      (rf_raddr_a_local),
      .rf_raddr_b_i      (rf_raddr_b_local),
      .rf_waddr_wb_i     (rf_waddr_wb_local),
      .rf_we_wb_i        (rf_we_wb_local),
      .rf_wdata_wb_ecc_i (rf_wdata_wb_ecc_local),
      .rf_rdata_a_ecc_i  (rf_rdata_a_ecc_local),
      .rf_rdata_b_ecc_i  (rf_rdata_b_ecc_local),

      .ic_tag_req_i      (ic_tag_req_local),
      .ic_tag_write_i    (ic_tag_write_local),
      .ic_tag_addr_i     (ic_tag_addr_local),
      .ic_tag_wdata_i    (ic_tag_wdata_local),
      .ic_tag_rdata_i    (ic_tag_rdata_local),
      .ic_data_req_i     (ic_data_req_local),
      .ic_data_write_i   (ic_data_write_local),
      .ic_data_addr_i    (ic_data_addr_local),
      .ic_data_wdata_i   (ic_data_wdata_local),
      .ic_data_rdata_i   (ic_data_rdata_local),

      .irq_software_i    (irq_software_local),
      .irq_timer_i       (irq_timer_local),
      .irq_external_i    (irq_external_local),
      .irq_fast_i        (irq_fast_local),
      .irq_nm_i          (irq_nm_local),
      .irq_pending_i     (irq_pending_local),

      .debug_req_i       (debug_req_local),
      .crash_dump_i      (crash_dump_local),

      .alert_minor_o     (lockstep_alert_minor_local),
      .alert_major_o     (lockstep_alert_major_local),
      .core_busy_i       (core_busy_local),
      .test_en_i         (test_en_i),
      .scan_rst_ni       (scan_rst_ni)
    );

    // Manually buffer the output signals.
    prim_buf u_prim_buf_alert_minor (
      .in_i(lockstep_alert_minor_local),
      .out_o(lockstep_alert_minor)
    );

    prim_buf u_prim_buf_alert_major (
      .in_i(lockstep_alert_major_local),
      .out_o(lockstep_alert_major)
    );

  end else begin : gen_no_lockstep
    assign lockstep_alert_major = 1'b0;
    assign lockstep_alert_minor = 1'b0;
    logic unused_scan;
    assign unused_scan = scan_rst_ni;
  end

  // TODO - need a config to reset all registers before the lockstep alert can be used
  logic unused_lockstep_alert_major;
  assign unused_lockstep_alert_major = lockstep_alert_major;

  assign alert_major_o = core_alert_major;// | lockstep_alert_major;
  assign alert_minor_o = core_alert_minor | lockstep_alert_minor;

  `ASSERT_KNOWN(IbexAlertMinorX, alert_minor_o)
  `ASSERT_KNOWN(IbexAlertMajorX, alert_major_o)

endmodule
