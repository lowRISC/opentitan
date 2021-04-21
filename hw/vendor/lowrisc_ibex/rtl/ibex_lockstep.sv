// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Ibex lockstep module
// This module instantiates a second copy of the core logic, and compares it's outputs against
// those from the main core. The second core runs synchronously with the main core, delayed by
// LockstepOffset cycles.
module ibex_lockstep import ibex_pkg::*; #(
    parameter int unsigned LockstepOffset    = 2,
    parameter bit          PMPEnable         = 1'b0,
    parameter int unsigned PMPGranularity    = 0,
    parameter int unsigned PMPNumRegions     = 4,
    parameter int unsigned MHPMCounterNum    = 0,
    parameter int unsigned MHPMCounterWidth  = 40,
    parameter bit          RV32E             = 1'b0,
    parameter rv32m_e      RV32M             = RV32MFast,
    parameter rv32b_e      RV32B             = RV32BNone,
    parameter bit          BranchTargetALU   = 1'b0,
    parameter bit          WritebackStage    = 1'b0,
    parameter bit          ICache            = 1'b0,
    parameter bit          ICacheECC         = 1'b0,
    parameter int unsigned BusSizeECC        = BUS_SIZE,
    parameter int unsigned TagSizeECC        = IC_TAG_SIZE,
    parameter int unsigned LineSizeECC       = IC_LINE_SIZE,
    parameter bit          BranchPredictor   = 1'b0,
    parameter bit          DbgTriggerEn      = 1'b0,
    parameter int unsigned DbgHwBreakNum     = 1,
    parameter bit          SecureIbex        = 1'b0,
    parameter bit          DummyInstructions = 1'b0,
    parameter bit          RegFileECC        = 1'b0,
    parameter int unsigned RegFileDataWidth  = 32,
    parameter int unsigned DmHaltAddr        = 32'h1A110800,
    parameter int unsigned DmExceptionAddr   = 32'h1A110808
) (
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic [31:0]                  hart_id_i,
    input  logic [31:0]                  boot_addr_i,

    input  logic                         instr_req_i,
    input  logic                         instr_gnt_i,
    input  logic                         instr_rvalid_i,
    input  logic [31:0]                  instr_addr_i,
    input  logic [31:0]                  instr_rdata_i,
    input  logic                         instr_err_i,

    input  logic                         data_req_i,
    input  logic                         data_gnt_i,
    input  logic                         data_rvalid_i,
    input  logic                         data_we_i,
    input  logic [3:0]                   data_be_i,
    input  logic [31:0]                  data_addr_i,
    input  logic [31:0]                  data_wdata_i,
    input  logic [31:0]                  data_rdata_i,
    input  logic                         data_err_i,

    input  logic                         dummy_instr_id_i,
    input  logic [4:0]                   rf_raddr_a_i,
    input  logic [4:0]                   rf_raddr_b_i,
    input  logic [4:0]                   rf_waddr_wb_i,
    input  logic                         rf_we_wb_i,
    input  logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_i,
    input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
    input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

    input  logic [IC_NUM_WAYS-1:0]       ic_tag_req_i,
    input  logic                         ic_tag_write_i,
    input  logic [IC_INDEX_W-1:0]        ic_tag_addr_i,
    input  logic [TagSizeECC-1:0]        ic_tag_wdata_i,
    input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
    input  logic [IC_NUM_WAYS-1:0]       ic_data_req_i,
    input  logic                         ic_data_write_i,
    input  logic [IC_INDEX_W-1:0]        ic_data_addr_i,
    input  logic [LineSizeECC-1:0]       ic_data_wdata_i,
    input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],

    input  logic                         irq_software_i,
    input  logic                         irq_timer_i,
    input  logic                         irq_external_i,
    input  logic [14:0]                  irq_fast_i,
    input  logic                         irq_nm_i,
    input  logic                         irq_pending_i,

    input  logic                         debug_req_i,
    input  crash_dump_t                  crash_dump_i,

    output logic                         alert_minor_o,
    output logic                         alert_major_o,
    input  logic                         core_busy_i,
    input  logic                         test_en_i,
    input  logic                         scan_rst_ni
);

  localparam int unsigned LockstepOffsetW = $clog2(LockstepOffset);

  //////////////////////
  // Reset generation //
  //////////////////////

  logic [LockstepOffsetW-1:0] rst_shadow_cnt_d, rst_shadow_cnt_q;
  // Internally generated resets cause IMPERFECTSCH warnings
  /* verilator lint_off IMPERFECTSCH */
  logic                       rst_shadow_set_d, rst_shadow_set_q;
  logic                       rst_shadow_n;
  /* verilator lint_on IMPERFECTSCH */

  assign rst_shadow_set_d = (rst_shadow_cnt_q == LockstepOffsetW'(LockstepOffset - 1));
  assign rst_shadow_cnt_d = rst_shadow_set_d ? rst_shadow_cnt_q :
                                               (rst_shadow_cnt_q + LockstepOffsetW'(1));

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rst_shadow_cnt_q <= '0;
      rst_shadow_set_q <= '0;
    end else begin
      rst_shadow_cnt_q <= rst_shadow_cnt_d;
      rst_shadow_set_q <= rst_shadow_set_d;
    end
  end

  assign rst_shadow_n = test_en_i ? scan_rst_ni : rst_shadow_set_q;

  //////////////////
  // Input delays //
  //////////////////

  typedef struct packed {
    logic                        instr_gnt;
    logic                        instr_rvalid;
    logic [31:0]                 instr_rdata;
    logic                        instr_err;
    logic                        data_gnt;
    logic                        data_rvalid;
    logic [31:0]                 data_rdata;
    logic                        data_err;
    logic [RegFileDataWidth-1:0] rf_rdata_a_ecc;
    logic [RegFileDataWidth-1:0] rf_rdata_b_ecc;
    logic                        irq_software;
    logic                        irq_timer;
    logic                        irq_external;
    logic [14:0]                 irq_fast;
    logic                        irq_nm;
    logic                        debug_req;
  } delayed_inputs_t;

  delayed_inputs_t [LockstepOffset-1:0] shadow_inputs_q;
  delayed_inputs_t                      shadow_inputs_in;
  // Packed arrays must be dealt with separately
  logic [TagSizeECC-1:0]                shadow_tag_rdata_q [IC_NUM_WAYS][LockstepOffset];
  logic [LineSizeECC-1:0]               shadow_data_rdata_q [IC_NUM_WAYS][LockstepOffset];

  // Assign the inputs to the delay structure
  assign shadow_inputs_in.instr_gnt      = instr_gnt_i;
  assign shadow_inputs_in.instr_rvalid   = instr_rvalid_i;
  assign shadow_inputs_in.instr_rdata    = instr_rdata_i;
  assign shadow_inputs_in.instr_err      = instr_err_i;
  assign shadow_inputs_in.data_gnt       = data_gnt_i;
  assign shadow_inputs_in.data_rvalid    = data_rvalid_i;
  assign shadow_inputs_in.data_rdata     = data_rdata_i;
  assign shadow_inputs_in.data_err       = data_err_i;
  assign shadow_inputs_in.rf_rdata_a_ecc = rf_rdata_a_ecc_i;
  assign shadow_inputs_in.rf_rdata_b_ecc = rf_rdata_b_ecc_i;
  assign shadow_inputs_in.irq_software   = irq_software_i;
  assign shadow_inputs_in.irq_timer      = irq_timer_i;
  assign shadow_inputs_in.irq_external   = irq_external_i;
  assign shadow_inputs_in.irq_fast       = irq_fast_i;
  assign shadow_inputs_in.irq_nm         = irq_nm_i;
  assign shadow_inputs_in.debug_req      = debug_req_i;

  // Delay the inputs
  always_ff @(posedge clk_i) begin
    for (int unsigned i = 0; i < LockstepOffset-1; i++) begin
      shadow_inputs_q[i]     <= shadow_inputs_q[i+1];
      shadow_tag_rdata_q[i]  <= shadow_tag_rdata_q[i+1];
      shadow_data_rdata_q[i] <= shadow_data_rdata_q[i+1];
    end
    shadow_inputs_q[LockstepOffset-1]     <= shadow_inputs_in;
    shadow_tag_rdata_q[LockstepOffset-1]  <= ic_tag_rdata_i;
    shadow_data_rdata_q[LockstepOffset-1] <= ic_data_rdata_i;
  end

  ///////////////////
  // Output delays //
  ///////////////////

  typedef struct packed {
    logic                        instr_req;
    logic [31:0]                 instr_addr;
    logic                        data_req;
    logic                        data_we;
    logic [3:0]                  data_be;
    logic [31:0]                 data_addr;
    logic [31:0]                 data_wdata;
    logic                        dummy_instr_id;
    logic [4:0]                  rf_raddr_a;
    logic [4:0]                  rf_raddr_b;
    logic [4:0]                  rf_waddr_wb;
    logic                        rf_we_wb;
    logic [RegFileDataWidth-1:0] rf_wdata_wb_ecc;
    logic [IC_NUM_WAYS-1:0]      ic_tag_req;
    logic                        ic_tag_write;
    logic [IC_INDEX_W-1:0]       ic_tag_addr;
    logic [TagSizeECC-1:0]       ic_tag_wdata;
    logic [IC_NUM_WAYS-1:0]      ic_data_req;
    logic                        ic_data_write;
    logic [IC_INDEX_W-1:0]       ic_data_addr;
    logic [LineSizeECC-1:0]      ic_data_wdata;
    logic                        irq_pending;
    crash_dump_t                 crash_dump;
    logic                        core_busy;
  } delayed_outputs_t;

  delayed_outputs_t [LockstepOffset-1:0] core_outputs_q;
  delayed_outputs_t                      core_outputs_in, shadow_outputs;

  // Assign core outputs to the structure
  assign core_outputs_in.instr_req       = instr_req_i;
  assign core_outputs_in.instr_addr      = instr_addr_i;
  assign core_outputs_in.data_req        = data_req_i;
  assign core_outputs_in.data_we         = data_we_i;
  assign core_outputs_in.data_be         = data_be_i;
  assign core_outputs_in.data_addr       = data_addr_i;
  assign core_outputs_in.data_wdata      = data_wdata_i;
  assign core_outputs_in.dummy_instr_id  = dummy_instr_id_i;
  assign core_outputs_in.rf_raddr_a      = rf_raddr_a_i;
  assign core_outputs_in.rf_raddr_b      = rf_raddr_b_i;
  assign core_outputs_in.rf_waddr_wb     = rf_waddr_wb_i;
  assign core_outputs_in.rf_we_wb        = rf_we_wb_i;
  assign core_outputs_in.rf_wdata_wb_ecc = rf_wdata_wb_ecc_i;
  assign core_outputs_in.ic_tag_req      = ic_tag_req_i;
  assign core_outputs_in.ic_tag_write    = ic_tag_write_i;
  assign core_outputs_in.ic_tag_addr     = ic_tag_addr_i;
  assign core_outputs_in.ic_tag_wdata    = ic_tag_wdata_i;
  assign core_outputs_in.ic_data_req     = ic_data_req_i;
  assign core_outputs_in.ic_data_write   = ic_data_write_i;
  assign core_outputs_in.ic_data_addr    = ic_data_addr_i;
  assign core_outputs_in.ic_data_wdata   = ic_data_wdata_i;
  assign core_outputs_in.irq_pending     = irq_pending_i;
  assign core_outputs_in.crash_dump      = crash_dump_i;
  assign core_outputs_in.core_busy       = core_busy_i;

  // Delay the outputs
  always_ff @(posedge clk_i) begin
    for (int unsigned i = 0; i < LockstepOffset-1; i++) begin
      core_outputs_q[i] <= core_outputs_q[i+1];
    end
    core_outputs_q[LockstepOffset-1] <= core_outputs_in;
  end

  ///////////////////////////////
  // Shadow core instantiation //
  ///////////////////////////////

  logic shadow_alert_minor, shadow_alert_major;

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
  ) u_shadow_core (
    .clk_i             (clk_i),
    .rst_ni            (rst_shadow_n),

    .hart_id_i         (hart_id_i),
    .boot_addr_i       (boot_addr_i),

    .instr_req_o       (shadow_outputs.instr_req),
    .instr_gnt_i       (shadow_inputs_q[0].instr_gnt),
    .instr_rvalid_i    (shadow_inputs_q[0].instr_rvalid),
    .instr_addr_o      (shadow_outputs.instr_addr),
    .instr_rdata_i     (shadow_inputs_q[0].instr_rdata),
    .instr_err_i       (shadow_inputs_q[0].instr_err),

    .data_req_o        (shadow_outputs.data_req),
    .data_gnt_i        (shadow_inputs_q[0].data_gnt),
    .data_rvalid_i     (shadow_inputs_q[0].data_rvalid),
    .data_we_o         (shadow_outputs.data_we),
    .data_be_o         (shadow_outputs.data_be),
    .data_addr_o       (shadow_outputs.data_addr),
    .data_wdata_o      (shadow_outputs.data_wdata),
    .data_rdata_i      (shadow_inputs_q[0].data_rdata),
    .data_err_i        (shadow_inputs_q[0].data_err),

    .dummy_instr_id_o  (shadow_outputs.dummy_instr_id),
    .rf_raddr_a_o      (shadow_outputs.rf_raddr_a),
    .rf_raddr_b_o      (shadow_outputs.rf_raddr_b),
    .rf_waddr_wb_o     (shadow_outputs.rf_waddr_wb),
    .rf_we_wb_o        (shadow_outputs.rf_we_wb),
    .rf_wdata_wb_ecc_o (shadow_outputs.rf_wdata_wb_ecc),
    .rf_rdata_a_ecc_i  (shadow_inputs_q[0].rf_rdata_a_ecc),
    .rf_rdata_b_ecc_i  (shadow_inputs_q[0].rf_rdata_b_ecc),

    .ic_tag_req_o      (shadow_outputs.ic_tag_req),
    .ic_tag_write_o    (shadow_outputs.ic_tag_write),
    .ic_tag_addr_o     (shadow_outputs.ic_tag_addr),
    .ic_tag_wdata_o    (shadow_outputs.ic_tag_wdata),
    .ic_tag_rdata_i    (shadow_tag_rdata_q[0]),
    .ic_data_req_o     (shadow_outputs.ic_data_req),
    .ic_data_write_o   (shadow_outputs.ic_data_write),
    .ic_data_addr_o    (shadow_outputs.ic_data_addr),
    .ic_data_wdata_o   (shadow_outputs.ic_data_wdata),
    .ic_data_rdata_i   (shadow_data_rdata_q[0]),

    .irq_software_i    (shadow_inputs_q[0].irq_software),
    .irq_timer_i       (shadow_inputs_q[0].irq_timer),
    .irq_external_i    (shadow_inputs_q[0].irq_external),
    .irq_fast_i        (shadow_inputs_q[0].irq_fast),
    .irq_nm_i          (shadow_inputs_q[0].irq_nm),
    .irq_pending_o     (shadow_outputs.irq_pending),

    .debug_req_i       (shadow_inputs_q[0].debug_req),
    .crash_dump_o      (shadow_outputs.crash_dump),

`ifdef RVFI
    .rvfi_valid        (),
    .rvfi_order        (),
    .rvfi_insn         (),
    .rvfi_trap         (),
    .rvfi_halt         (),
    .rvfi_intr         (),
    .rvfi_mode         (),
    .rvfi_ixl          (),
    .rvfi_rs1_addr     (),
    .rvfi_rs2_addr     (),
    .rvfi_rs3_addr     (),
    .rvfi_rs1_rdata    (),
    .rvfi_rs2_rdata    (),
    .rvfi_rs3_rdata    (),
    .rvfi_rd_addr      (),
    .rvfi_rd_wdata     (),
    .rvfi_pc_rdata     (),
    .rvfi_pc_wdata     (),
    .rvfi_mem_addr     (),
    .rvfi_mem_rmask    (),
    .rvfi_mem_wmask    (),
    .rvfi_mem_rdata    (),
    .rvfi_mem_wdata    (),
`endif

    .alert_minor_o     (shadow_alert_minor),
    .alert_major_o     (shadow_alert_major),
    .core_busy_o       (shadow_outputs.core_busy)
  );

  /////////////////////////
  // Compare the outputs //
  /////////////////////////

  logic outputs_mismatch;

  // TODO evaluate the timing here - might need to register shadow_outputs
  assign outputs_mismatch = rst_shadow_n & (shadow_outputs != core_outputs_q[0]);
  assign alert_major_o    = outputs_mismatch | shadow_alert_major;
  assign alert_minor_o    = shadow_alert_minor;

endmodule
