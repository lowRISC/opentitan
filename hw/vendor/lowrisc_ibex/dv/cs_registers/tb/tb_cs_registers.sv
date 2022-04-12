// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb_cs_registers #(
    parameter bit               DbgTriggerEn     = 1'b0,
    parameter bit               ICache           = 1'b0,
    parameter int unsigned      MHPMCounterNum   = 8,
    parameter int unsigned      MHPMCounterWidth = 40,
    parameter bit               PMPEnable        = 1'b0,
    parameter int unsigned      PMPGranularity   = 0,
    parameter int unsigned      PMPNumRegions    = 4,
    parameter bit               RV32E            = 1'b0,
    parameter ibex_pkg::rv32m_e RV32M            = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e RV32B            = ibex_pkg::RV32BNone
) (
    // Clock and Reset
    inout  logic                clk_i,
    inout  logic                in_rst_ni,
    output logic                test_passed_o
);

  logic                 dpi_rst_ni;
  logic                 rst_ni;

  // Interface to registers (SRAM like)
  logic                 csr_access_i;
  ibex_pkg::csr_num_e   csr_addr_i;
  logic [31:0]          csr_wdata_i;
  ibex_pkg::csr_op_e    csr_op_i;
  logic                 csr_op_en_i;
  logic [31:0]          csr_rdata_o;

  logic                 illegal_csr_insn_o;

  logic                 csr_access_d;
  ibex_pkg::csr_num_e   csr_addr_d;
  logic [31:0]          csr_wdata_d;
  ibex_pkg::csr_op_e    csr_op_d;
  logic                 csr_op_en_d;
  //-----------------
  // Reset generation
  //-----------------
  // Allow reset to be toggled by the top-level (in Verilator)
  // or a DPI call
  assign rst_ni = in_rst_ni & dpi_rst_ni;

  //----------------------------------------
  // Clock generation (not used in Verilator
  //----------------------------------------
`ifndef VERILATOR
  logic local_clk_i;
  initial begin
    local_clk_i = 1'b0;
    while (1) begin
      #10
      local_clk_i = !local_clk_i;
    end
  end
  assign clk_i = local_clk_i;
  assign in_rst_ni = 1'b1;
`endif

  /* verilator lint_off PINMISSING */
  ibex_cs_registers #(
    .DbgTriggerEn     (DbgTriggerEn),
    .ICache           (ICache),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B)
  ) i_cs_regs (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .csr_access_i       (csr_access_i),
    .csr_addr_i         (csr_addr_i),
    .csr_wdata_i        (csr_wdata_i),
    .csr_op_i           (csr_op_i),
    .csr_op_en_i        (csr_op_en_i),
    .csr_rdata_o        (csr_rdata_o),
    .illegal_csr_insn_o (illegal_csr_insn_o)
  );
  /* verilator lint_on PINMISSING */

  // DPI calls
  bit stop_simulation;
  bit test_passed;
  bit [31:0] seed;

  initial begin
    if (!$value$plusargs ("ntb_random_seed=%d", seed)) begin
      seed = 32'd0;
    end
    env_dpi::env_initial(seed,
        PMPEnable, PMPGranularity, PMPNumRegions,
        MHPMCounterNum, MHPMCounterWidth);
  end

  final begin
    env_dpi::env_final();
  end

  always_ff @(posedge clk_i) begin
    env_dpi::env_tick(stop_simulation, test_passed);
    rst_dpi::rst_tick("rstn_driver", dpi_rst_ni);
    if (stop_simulation) begin
      $finish();
    end
  end

  // Signal test pass / fail as an output (Verilator sims can pick this up and use it as a
  // return code)
  assign test_passed_o = test_passed;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    reg_dpi::monitor_tick("reg_driver",
                          rst_ni,
                          illegal_csr_insn_o,
                          csr_access_i,
                          csr_op_i,
                          csr_op_en_i,
                          csr_addr_i,
                          csr_wdata_i,
                          csr_rdata_o);

    reg_dpi::driver_tick("reg_driver",
                         csr_access_d,
                         csr_op_d,
                         csr_op_en_d,
                         csr_addr_d,
                         csr_wdata_d);

    // Use NBA to drive inputs to ensure correct scheduling.
    // This always_ff block will be executed on the positive edge of the clock with undefined order
    // vs all other always_ff triggered on the positive edge of the clock. If `driver_tick` drives
    // the inputs directly some of the always_ff blocks will see the old version of the inputs and
    // others will see the new version depending on scheduling order. This schedules all the inputs
    // to be NBA updates to avoid the race condition (in effect acting like any other always_ff
    // block with the _d values being computed via DPI rather than combinational logic).
    csr_access_i <= csr_access_d;
    csr_addr_i <= csr_addr_d;
    csr_wdata_i <= csr_wdata_d;
    csr_op_i <= csr_op_d;
    csr_op_en_i <= csr_op_en_d;
  end

endmodule
