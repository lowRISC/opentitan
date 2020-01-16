// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb_cs_registers #(
    parameter bit          DbgTriggerEn     = 0,
    parameter int unsigned MHPMCounterNum   = 8,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit          PMPEnable        = 0,
    parameter int unsigned PMPGranularity   = 0,
    parameter int unsigned PMPNumRegions    = 4,
    parameter bit          RV32E            = 0,
    parameter bit          RV32M            = 0
) (
    // Clock and Reset
    inout  wire                 clk_i,
    inout  wire                 in_rst_ni,
    output wire                 test_passed_o
);

  logic                 dpi_rst_ni;
  logic                 rst_ni;
  logic [31:0]          hart_id_i;

  // Privilege mode
  ibex_pkg::priv_lvl_e  priv_mode_id_o;
  ibex_pkg::priv_lvl_e  priv_mode_if_o;
  ibex_pkg::priv_lvl_e  priv_mode_lsu_o;
  logic                 csr_mstatus_tw_o;

  // mtvec
  logic [31:0]          csr_mtvec_o;
  logic                 csr_mtvec_init_i;
  logic [31:0]          boot_addr_i;

  // Interface to registers (SRAM like)
  logic                 csr_access_i;
  ibex_pkg::csr_num_e   csr_addr_i;
  logic [31:0]          csr_wdata_i;
  ibex_pkg::csr_op_e    csr_op_i;
  logic [31:0]          csr_rdata_o;

  // interrupts
  logic                 irq_software_i;
  logic                 irq_timer_i;
  logic                 irq_external_i;
  logic [14:0]          irq_fast_i;
  logic                 irq_pending_o;          // interupt request pending
  logic                 nmi_mode_i;             // core is handling an NMI
  logic                 csr_msip_o;             // software interrupt pending
  logic                 csr_mtip_o;             // timer interrupt pending
  logic                 csr_meip_o;             // external interrupt pending
  logic [14:0]          csr_mfip_o;             // fast interrupt pending
  logic                 csr_mstatus_mie_o;
  logic [31:0]          csr_mepc_o;

    // PMP
  ibex_pkg::pmp_cfg_t   csr_pmp_cfg_o  [PMPNumRegions];
  logic [33:0]          csr_pmp_addr_o [PMPNumRegions];

  // debug
  logic                 debug_mode_i;
  ibex_pkg::dbg_cause_e debug_cause_i;
  logic                 debug_csr_save_i;
  logic [31:0]          csr_depc_o;
  logic                 debug_single_step_o;
  logic                 debug_ebreakm_o;
  logic                 debug_ebreaku_o;
  logic                 trigger_match_o;

  logic [31:0]          pc_if_i;
  logic [31:0]          pc_id_i;

  logic                 csr_save_if_i;
  logic                 csr_save_id_i;
  logic                 csr_restore_mret_i;
  logic                 csr_restore_dret_i;
  logic                 csr_save_cause_i;
  ibex_pkg::exc_cause_e csr_mcause_i;
  logic [31:0]          csr_mtval_i;
  logic                 illegal_csr_insn_o;     // access to non-existent CSR,
                                                // with wrong priviledge level, or
                                                // missing write permissions
  logic                 instr_new_id_i;         // ID stage sees a new instr

  // Performance Counters
  logic                 instr_ret_i;            // instr retired in ID/EX stage
  logic                 instr_ret_compressed_i; // compressed instr retired
  logic                 imiss_i;                // instr fetch
  logic                 pc_set_i;               // PC was set to a new value
  logic                 jump_i;                 // jump instr seen (j, jr, jal, jalr)
  logic                 branch_i;               // branch instr seen (bf, bnf)
  logic                 branch_taken_i;         // branch was taken
  logic                 mem_load_i;             // load from memory in this cycle
  logic                 mem_store_i;            // store to memory in this cycle
  logic                 lsu_busy_i;

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

  ibex_cs_registers #(
    .DbgTriggerEn     (DbgTriggerEn),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .RV32E            (RV32E),
    .RV32M            (RV32M)
  ) i_cs_regs (.*);

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
                          csr_addr_i,
                          csr_wdata_i,
                          csr_rdata_o);
    reg_dpi::driver_tick("reg_driver",
                         csr_access_i,
                         csr_op_i,
                         csr_addr_i,
                         csr_wdata_i);
  end
  // Note that CSR accesses only happen if instr_new_id_i is high
  assign instr_new_id_i = csr_access_i;

endmodule
