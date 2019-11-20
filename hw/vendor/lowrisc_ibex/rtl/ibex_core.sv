// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_core #(
    parameter bit          PMPEnable                = 1'b0,
    parameter int unsigned PMPGranularity           = 0,
    parameter int unsigned PMPNumRegions            = 4,
    parameter int unsigned MHPMCounterNum           = 0,
    parameter int unsigned MHPMCounterWidth         = 40,
    parameter bit          RV32E                    = 1'b0,
    parameter bit          RV32M                    = 1'b1,
    parameter              MultiplierImplementation = "fast",
    parameter int unsigned DmHaltAddr               = 32'h1A110800,
    parameter int unsigned DmExceptionAddr          = 32'h1A110808
) (
    // Clock and Reset
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        test_en_i,     // enable all clock gates for testing

    input  logic [31:0] hart_id_i,
    input  logic [31:0] boot_addr_i,

    // Instruction memory interface
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    input  logic        instr_rvalid_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,
    input  logic        instr_err_i,

    // Data memory interface
    output logic        data_req_o,
    input  logic        data_gnt_i,
    input  logic        data_rvalid_i,
    output logic        data_we_o,
    output logic [3:0]  data_be_o,
    output logic [31:0] data_addr_o,
    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,
    input  logic        data_err_i,

    // Interrupt inputs
    input  logic        irq_software_i,
    input  logic        irq_timer_i,
    input  logic        irq_external_i,
    input  logic [14:0] irq_fast_i,
    input  logic        irq_nm_i,       // non-maskeable interrupt

    // Debug Interface
    input  logic        debug_req_i,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
`endif

    // CPU Control Signals
    input  logic        fetch_enable_i,
    output logic        core_sleep_o
);

  import ibex_pkg::*;

  localparam int unsigned PMP_NUM_CHAN = 2;

  // IF/ID signals
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;         // Instruction sampled inside IF stage
  logic [15:0] instr_rdata_c_id;       // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_fetch_err;        // Bus error on instr fetch
  logic        illegal_c_insn_id;      // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                  // Program counter in IF stage
  logic [31:0] pc_id;                  // Program counter in ID stage

  logic        instr_valid_clear;
  logic        pc_set;
  pc_sel_e     pc_mux_id;              // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;          // Mux selector for exception PC
  exc_cause_e  exc_cause;              // Exception cause

  logic        lsu_load_err;
  logic        lsu_store_err;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] jump_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;
  logic        core_busy_d, core_busy_q;

  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] regfile_wdata_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;

  // CSR control
  logic        csr_access;
  logic        valid_csr_id;
  csr_op_e     csr_op;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong priviledge level,
                                       // or missing write permissions

  // Data Memory Control
  logic        data_we_ex;
  logic [1:0]  data_type_ex;
  logic        data_sign_ext_ex;
  logic        data_req_ex;
  logic [31:0] data_wdata_ex;
  logic [31:0] regfile_wdata_lsu;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_data_valid;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface

  // Interrupts
  logic        irq_pending;
  logic        csr_msip;
  logic        csr_mtip;
  logic        csr_meip;
  logic [14:0] csr_mfip;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0] csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg  [PMPNumRegions];
  logic        pmp_req_err  [PMP_NUM_CHAN];
  logic        instr_req_out;
  logic        data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_if;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;

  // performance counter related signals
  logic        instr_ret;
  logic        instr_ret_compressed;
  logic        perf_imiss;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  // RISC-V Formal Interface signals
`ifdef RVFI
  logic        rvfi_intr_d;
  logic        rvfi_set_trap_pc_d;
  logic        rvfi_set_trap_pc_q;
  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_id;
  logic [4:0]  rvfi_rs2_addr_id;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_id;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_id;
  logic [31:0] rvfi_rs2_data_q;
  logic [4:0]  rvfi_rd_addr_id;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_id;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_id;
  logic        rvfi_insn_new_d;
  logic        rvfi_insn_new_q;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
`endif

  //////////////////////
  // Clock management //
  //////////////////////

  logic        clk;

  logic        clock_en;

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
  assign core_busy_d = ctrl_busy | if_busy | lsu_busy;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      core_busy_q <= 1'b0;
    end else begin
      core_busy_q <= core_busy_d;
    end
  end

  assign clock_en     = core_busy_q | debug_req_i | irq_pending | irq_nm_i;
  assign core_sleep_o = ~clock_en;

  // main clock gate of the core
  // generates all clocks except the one for the debug unit which is
  // independent
  prim_clock_gating core_clock_gate_i (
      .clk_i     ( clk_i           ),
      .en_i      ( clock_en        ),
      .test_en_i ( test_en_i       ),
      .clk_o     ( clk             )
  );

  //////////////
  // IF stage //
  //////////////

  ibex_if_stage #(
      .DmHaltAddr       ( DmHaltAddr      ),
      .DmExceptionAddr  ( DmExceptionAddr )
  ) if_stage_i (
      .clk_i                    ( clk                    ),
      .rst_ni                   ( rst_ni                 ),

      .boot_addr_i              ( boot_addr_i            ),
      .req_i                    ( instr_req_int          ), // instruction request control

      // instruction cache interface
      .instr_req_o              ( instr_req_out          ),
      .instr_addr_o             ( instr_addr_o           ),
      .instr_gnt_i              ( instr_gnt_i            ),
      .instr_rvalid_i           ( instr_rvalid_i         ),
      .instr_rdata_i            ( instr_rdata_i          ),
      .instr_err_i              ( instr_err_i            ),
      .instr_pmp_err_i          ( pmp_req_err[PMP_I]     ),

      // outputs to ID stage
      .instr_valid_id_o         ( instr_valid_id         ),
      .instr_new_id_o           ( instr_new_id           ),
      .instr_rdata_id_o         ( instr_rdata_id         ),
      .instr_rdata_c_id_o       ( instr_rdata_c_id       ),
      .instr_is_compressed_id_o ( instr_is_compressed_id ),
      .instr_fetch_err_o        ( instr_fetch_err        ),
      .illegal_c_insn_id_o      ( illegal_c_insn_id      ),
      .pc_if_o                  ( pc_if                  ),
      .pc_id_o                  ( pc_id                  ),

      // control signals
      .instr_valid_clear_i      ( instr_valid_clear      ),
      .pc_set_i                 ( pc_set                 ),
      .pc_mux_i                 ( pc_mux_id              ),
      .exc_pc_mux_i             ( exc_pc_mux_id          ),
      .exc_cause                ( exc_cause              ),

      // jump targets
      .jump_target_ex_i         ( jump_target_ex         ),

      // CSRs
      .csr_mepc_i               ( csr_mepc               ), // exception return address
      .csr_depc_i               ( csr_depc               ), // debug return address
      .csr_mtvec_i              ( csr_mtvec              ), // trap-vector base address
      .csr_mtvec_init_o         ( csr_mtvec_init         ),

      // pipeline stalls
      .id_in_ready_i            ( id_in_ready            ),

      .if_busy_o                ( if_busy                ),
      .perf_imiss_o             ( perf_imiss             )
  );

  // Qualify the instruction request with PMP error
  assign instr_req_o = instr_req_out & ~pmp_req_err[PMP_I];

  //////////////
  // ID stage //
  //////////////

  ibex_id_stage #(
      .RV32E ( RV32E ),
      .RV32M ( RV32M )
  ) id_stage_i (
      .clk_i                        ( clk                    ),
      .rst_ni                       ( rst_ni                 ),

      .test_en_i                    ( test_en_i              ),

      // Processor Enable
      .fetch_enable_i               ( fetch_enable_i         ),
      .ctrl_busy_o                  ( ctrl_busy              ),
      .illegal_insn_o               ( illegal_insn_id        ),

      // from/to IF-ID pipeline register
      .instr_valid_i                ( instr_valid_id         ),
      .instr_new_i                  ( instr_new_id           ),
      .instr_rdata_i                ( instr_rdata_id         ),
      .instr_rdata_c_i              ( instr_rdata_c_id       ),
      .instr_is_compressed_i        ( instr_is_compressed_id ),

      // Jumps and branches
      .branch_decision_i            ( branch_decision        ),

      // IF and ID control signals
      .id_in_ready_o                ( id_in_ready            ),
      .instr_valid_clear_o          ( instr_valid_clear      ),
      .instr_req_o                  ( instr_req_int          ),
      .pc_set_o                     ( pc_set                 ),
      .pc_mux_o                     ( pc_mux_id              ),
      .exc_pc_mux_o                 ( exc_pc_mux_id          ),
      .exc_cause_o                  ( exc_cause              ),

      .instr_fetch_err_i            ( instr_fetch_err        ),
      .illegal_c_insn_i             ( illegal_c_insn_id      ),

      .pc_id_i                      ( pc_id                  ),

      // Stalls
      .ex_valid_i                   ( ex_valid               ),
      .lsu_valid_i                  ( lsu_data_valid         ),

      .alu_operator_ex_o            ( alu_operator_ex        ),
      .alu_operand_a_ex_o           ( alu_operand_a_ex       ),
      .alu_operand_b_ex_o           ( alu_operand_b_ex       ),

      .mult_en_ex_o                 ( mult_en_ex             ),
      .div_en_ex_o                  ( div_en_ex              ),
      .multdiv_operator_ex_o        ( multdiv_operator_ex    ),
      .multdiv_signed_mode_ex_o     ( multdiv_signed_mode_ex ),
      .multdiv_operand_a_ex_o       ( multdiv_operand_a_ex   ),
      .multdiv_operand_b_ex_o       ( multdiv_operand_b_ex   ),

      // CSR ID/EX
      .csr_access_o                 ( csr_access             ),
      .csr_op_o                     ( csr_op                 ),
      .csr_save_if_o                ( csr_save_if            ), // control signal to save PC
      .csr_save_id_o                ( csr_save_id            ), // control signal to save PC
      .csr_restore_mret_id_o        ( csr_restore_mret_id    ), // restore mstatus upon DRET
      .csr_restore_dret_id_o        ( csr_restore_dret_id    ), // restore mstatus upon MRET
      .csr_save_cause_o             ( csr_save_cause         ),
      .csr_mtval_o                  ( csr_mtval              ),
      .priv_mode_i                  ( priv_mode_id           ),
      .csr_mstatus_tw_i             ( csr_mstatus_tw         ),
      .illegal_csr_insn_i           ( illegal_csr_insn_id    ),

      // LSU
      .data_req_ex_o                ( data_req_ex            ), // to load store unit
      .data_we_ex_o                 ( data_we_ex             ), // to load store unit
      .data_type_ex_o               ( data_type_ex           ), // to load store unit
      .data_sign_ext_ex_o           ( data_sign_ext_ex       ), // to load store unit
      .data_wdata_ex_o              ( data_wdata_ex          ), // to load store unit

      .lsu_addr_incr_req_i          ( lsu_addr_incr_req      ),
      .lsu_addr_last_i              ( lsu_addr_last          ),

      .lsu_load_err_i               ( lsu_load_err           ),
      .lsu_store_err_i              ( lsu_store_err          ),

      // Interrupt Signals
      .csr_mstatus_mie_i            ( csr_mstatus_mie        ),
      .csr_msip_i                   ( csr_msip               ),
      .csr_mtip_i                   ( csr_mtip               ),
      .csr_meip_i                   ( csr_meip               ),
      .csr_mfip_i                   ( csr_mfip               ),
      .irq_pending_i                ( irq_pending            ),
      .irq_nm_i                     ( irq_nm_i               ),

      // Debug Signal
      .debug_mode_o                 ( debug_mode             ),
      .debug_cause_o                ( debug_cause            ),
      .debug_csr_save_o             ( debug_csr_save         ),
      .debug_req_i                  ( debug_req_i            ),
      .debug_single_step_i          ( debug_single_step      ),
      .debug_ebreakm_i              ( debug_ebreakm          ),
      .debug_ebreaku_i              ( debug_ebreaku          ),

      // write data to commit in the register file
      .regfile_wdata_lsu_i          ( regfile_wdata_lsu      ),
      .regfile_wdata_ex_i           ( regfile_wdata_ex       ),
      .csr_rdata_i                  ( csr_rdata              ),

`ifdef RVFI
      .rfvi_reg_raddr_ra_o          ( rvfi_rs1_addr_id       ),
      .rfvi_reg_rdata_ra_o          ( rvfi_rs1_data_id       ),
      .rfvi_reg_raddr_rb_o          ( rvfi_rs2_addr_id       ),
      .rfvi_reg_rdata_rb_o          ( rvfi_rs2_data_id       ),
      .rfvi_reg_waddr_rd_o          ( rvfi_rd_addr_id        ),
      .rfvi_reg_wdata_rd_o          ( rvfi_rd_wdata_id       ),
      .rfvi_reg_we_o                ( rvfi_rd_we_id          ),
`endif

      // Performance Counters
      .perf_jump_o                  ( perf_jump              ),
      .perf_branch_o                ( perf_branch            ),
      .perf_tbranch_o               ( perf_tbranch           ),
      .instr_ret_o                  ( instr_ret              ),
      .instr_ret_compressed_o       ( instr_ret_compressed   )
  );

  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  ibex_ex_block #(
      .RV32M                      ( RV32M                    ),
      .MultiplierImplementation   ( MultiplierImplementation )
  ) ex_block_i (
      .clk_i                      ( clk                      ),
      .rst_ni                     ( rst_ni                   ),

      // ALU signal from ID stage
      .alu_operator_i             ( alu_operator_ex          ),
      .alu_operand_a_i            ( alu_operand_a_ex         ),
      .alu_operand_b_i            ( alu_operand_b_ex         ),

      // Multipler/Divider signal from ID stage
      .multdiv_operator_i         ( multdiv_operator_ex      ),
      .mult_en_i                  ( mult_en_ex               ),
      .div_en_i                   ( div_en_ex                ),
      .multdiv_signed_mode_i      ( multdiv_signed_mode_ex   ),
      .multdiv_operand_a_i        ( multdiv_operand_a_ex     ),
      .multdiv_operand_b_i        ( multdiv_operand_b_ex     ),

      // Outputs
      .alu_adder_result_ex_o      ( alu_adder_result_ex      ), // to LSU
      .regfile_wdata_ex_o         ( regfile_wdata_ex         ), // to ID

      .jump_target_o              ( jump_target_ex           ), // to IF
      .branch_decision_o          ( branch_decision          ), // to ID

      .ex_valid_o                 ( ex_valid                 )
  );

  /////////////////////
  // Load/store unit //
  /////////////////////

  assign data_req_o = data_req_out & ~pmp_req_err[PMP_D];

  ibex_load_store_unit  load_store_unit_i (
      .clk_i                 ( clk                 ),
      .rst_ni                ( rst_ni              ),

      // data interface
      .data_req_o            ( data_req_out        ),
      .data_gnt_i            ( data_gnt_i          ),
      .data_rvalid_i         ( data_rvalid_i       ),
      .data_err_i            ( data_err_i          ),
      .data_pmp_err_i        ( pmp_req_err[PMP_D]  ),

      .data_addr_o           ( data_addr_o         ),
      .data_we_o             ( data_we_o           ),
      .data_be_o             ( data_be_o           ),
      .data_wdata_o          ( data_wdata_o        ),
      .data_rdata_i          ( data_rdata_i        ),

      // signals to/from ID/EX stage
      .data_we_ex_i          ( data_we_ex          ),
      .data_type_ex_i        ( data_type_ex        ),
      .data_wdata_ex_i       ( data_wdata_ex       ),
      .data_sign_ext_ex_i    ( data_sign_ext_ex    ),

      .data_rdata_ex_o       ( regfile_wdata_lsu   ),
      .data_req_ex_i         ( data_req_ex         ),

      .adder_result_ex_i     ( alu_adder_result_ex ),

      .addr_incr_req_o       ( lsu_addr_incr_req   ),
      .addr_last_o           ( lsu_addr_last       ),
      .data_valid_o          ( lsu_data_valid      ),

      // exception signals
      .load_err_o            ( lsu_load_err        ),
      .store_err_o           ( lsu_store_err       ),

      .busy_o                ( lsu_busy            )
  );


  /////////////////////////////////////////
  // CSRs (Control and Status Registers) //
  /////////////////////////////////////////

  assign csr_wdata  = alu_operand_a_ex;
  assign csr_addr   = csr_num_e'(csr_access ? alu_operand_b_ex[11:0] : 12'b0);

  assign perf_load  = data_req_o & data_gnt_i & (~data_we_o);
  assign perf_store = data_req_o & data_gnt_i & data_we_o;

  // CSR access is qualified by instruction fetch error
  assign valid_csr_id = instr_new_id & ~instr_fetch_err;

  ibex_cs_registers #(
      .MHPMCounterNum   ( MHPMCounterNum   ),
      .MHPMCounterWidth ( MHPMCounterWidth ),
      .PMPEnable        ( PMPEnable        ),
      .PMPGranularity   ( PMPGranularity   ),
      .PMPNumRegions    ( PMPNumRegions    ),
      .RV32E            ( RV32E            ),
      .RV32M            ( RV32M            )
  ) cs_registers_i (
      .clk_i                   ( clk                    ),
      .rst_ni                  ( rst_ni                 ),

      // Hart ID from outside
      .hart_id_i               ( hart_id_i              ),
      .priv_mode_id_o          ( priv_mode_id           ),
      .priv_mode_if_o          ( priv_mode_if           ),
      .priv_mode_lsu_o         ( priv_mode_lsu          ),

      // mtvec
      .csr_mtvec_o             ( csr_mtvec              ),
      .csr_mtvec_init_i        ( csr_mtvec_init         ),
      .boot_addr_i             ( boot_addr_i            ),

      // Interface to CSRs (SRAM like)
      .csr_access_i            ( csr_access             ),
      .csr_addr_i              ( csr_addr               ),
      .csr_wdata_i             ( csr_wdata              ),
      .csr_op_i                ( csr_op                 ),
      .csr_rdata_o             ( csr_rdata              ),

      // Interrupt related control signals
      .irq_software_i          ( irq_software_i         ),
      .irq_timer_i             ( irq_timer_i            ),
      .irq_external_i          ( irq_external_i         ),
      .irq_fast_i              ( irq_fast_i             ),
      .irq_pending_o           ( irq_pending            ),
      .csr_msip_o              ( csr_msip               ),
      .csr_mtip_o              ( csr_mtip               ),
      .csr_meip_o              ( csr_meip               ),
      .csr_mfip_o              ( csr_mfip               ),
      .csr_mstatus_mie_o       ( csr_mstatus_mie        ),
      .csr_mstatus_tw_o        ( csr_mstatus_tw         ),
      .csr_mepc_o              ( csr_mepc               ),

      // PMP
      .csr_pmp_cfg_o           ( csr_pmp_cfg            ),
      .csr_pmp_addr_o          ( csr_pmp_addr           ),

      // debug
      .csr_depc_o              ( csr_depc               ),
      .debug_mode_i            ( debug_mode             ),
      .debug_cause_i           ( debug_cause            ),
      .debug_csr_save_i        ( debug_csr_save         ),
      .debug_single_step_o     ( debug_single_step      ),
      .debug_ebreakm_o         ( debug_ebreakm          ),
      .debug_ebreaku_o         ( debug_ebreaku          ),

      .pc_if_i                 ( pc_if                  ),
      .pc_id_i                 ( pc_id                  ),

      .csr_save_if_i           ( csr_save_if            ),
      .csr_save_id_i           ( csr_save_id            ),
      .csr_restore_mret_i      ( csr_restore_mret_id    ),
      .csr_restore_dret_i      ( csr_restore_dret_id    ),
      .csr_save_cause_i        ( csr_save_cause         ),
      .csr_mcause_i            ( exc_cause              ),
      .csr_mtval_i             ( csr_mtval              ),
      .illegal_csr_insn_o      ( illegal_csr_insn_id    ),

      .instr_new_id_i          ( valid_csr_id           ),

      // performance counter related signals
      .instr_ret_i             ( instr_ret              ),
      .instr_ret_compressed_i  ( instr_ret_compressed   ),
      .imiss_i                 ( perf_imiss             ),
      .pc_set_i                ( pc_set                 ),
      .jump_i                  ( perf_jump              ),
      .branch_i                ( perf_branch            ),
      .branch_taken_i          ( perf_tbranch           ),
      .mem_load_i              ( perf_load              ),
      .mem_store_i             ( perf_store             ),
      .lsu_busy_i              ( lsu_busy               )
  );

  if (PMPEnable) begin : g_pmp
    logic [33:0] pmp_req_addr [PMP_NUM_CHAN];
    pmp_req_e    pmp_req_type [PMP_NUM_CHAN];
    priv_lvl_e   pmp_priv_lvl [PMP_NUM_CHAN];

    assign pmp_req_addr[PMP_I] = {2'b00,instr_addr_o[31:0]};
    assign pmp_req_type[PMP_I] = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I] = priv_mode_if;
    assign pmp_req_addr[PMP_D] = {2'b00,data_addr_o[31:0]};
    assign pmp_req_type[PMP_D] = data_we_o ? PMP_ACC_WRITE : PMP_ACC_READ;
    assign pmp_priv_lvl[PMP_D] = priv_mode_lsu;

    ibex_pmp #(
        .PMPGranularity        ( PMPGranularity ),
        .PMPNumChan            ( PMP_NUM_CHAN   ),
        .PMPNumRegions         ( PMPNumRegions  )
    ) pmp_i (
        .clk_i                 ( clk            ),
        .rst_ni                ( rst_ni         ),
        // Interface to CSRs
        .csr_pmp_cfg_i         ( csr_pmp_cfg    ),
        .csr_pmp_addr_i        ( csr_pmp_addr   ),
        .priv_mode_i           ( pmp_priv_lvl   ),
        // Access checking channels
        .pmp_req_addr_i        ( pmp_req_addr   ),
        .pmp_req_type_i        ( pmp_req_type   ),
        .pmp_req_err_o         ( pmp_req_err    )
    );
  end else begin : g_no_pmp
    // Unused signal tieoff
    priv_lvl_e unused_priv_lvl_if, unused_priv_lvl_ls;
    logic [33:0] unused_csr_pmp_addr [PMPNumRegions];
    pmp_cfg_t    unused_csr_pmp_cfg  [PMPNumRegions];
    assign unused_priv_lvl_if = priv_mode_if;
    assign unused_priv_lvl_ls = priv_mode_lsu;
    assign unused_csr_pmp_addr = csr_pmp_addr;
    assign unused_csr_pmp_cfg = csr_pmp_cfg;

    // Output tieoff
    assign pmp_req_err[PMP_I] = 1'b0;
    assign pmp_req_err[PMP_D] = 1'b0;
  end

`ifdef RVFI
  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_halt              <= '0;
      rvfi_trap              <= '0;
      rvfi_intr              <= '0;
      rvfi_order             <= '0;
      rvfi_insn              <= '0;
      rvfi_mode              <= {PRIV_LVL_M};
      rvfi_rs1_addr          <= '0;
      rvfi_rs2_addr          <= '0;
      rvfi_pc_rdata          <= '0;
      rvfi_pc_wdata          <= '0;
      rvfi_mem_rmask         <= '0;
      rvfi_mem_wmask         <= '0;
      rvfi_valid             <= '0;
      rvfi_rs1_rdata         <= '0;
      rvfi_rs2_rdata         <= '0;
      rvfi_rd_wdata          <= '0;
      rvfi_rd_addr           <= '0;
      rvfi_mem_rdata         <= '0;
      rvfi_mem_wdata         <= '0;
      rvfi_mem_addr          <= '0;
    end else begin
      rvfi_halt              <= '0;
      rvfi_trap              <= illegal_insn_id;
      rvfi_intr              <= rvfi_intr_d;
      rvfi_order             <= rvfi_order + 64'(rvfi_valid);
      rvfi_insn              <= rvfi_insn_id;
      rvfi_mode              <= {priv_mode_id};
      rvfi_rs1_addr          <= rvfi_rs1_addr_id;
      rvfi_rs2_addr          <= rvfi_rs2_addr_id;
      rvfi_pc_rdata          <= pc_id;
      rvfi_pc_wdata          <= pc_if;
      rvfi_mem_rmask         <= rvfi_mem_mask_int;
      rvfi_mem_wmask         <= data_we_o ? rvfi_mem_mask_int : 4'b0000;
      rvfi_valid             <= instr_ret;
      rvfi_rs1_rdata         <= rvfi_rs1_data_d;
      rvfi_rs2_rdata         <= rvfi_rs2_data_d;
      rvfi_rd_wdata          <= rvfi_rd_wdata_d;
      rvfi_rd_addr           <= rvfi_rd_addr_d;
      rvfi_mem_rdata         <= rvfi_mem_rdata_d;
      rvfi_mem_wdata         <= rvfi_mem_wdata_d;
      rvfi_mem_addr          <= rvfi_mem_addr_d;
    end
  end

  // Keep the mem data stable for each instruction cycle
  always_comb begin
    if (rvfi_insn_new_d && lsu_data_valid) begin
      rvfi_mem_addr_d  = alu_adder_result_ex;
      rvfi_mem_rdata_d = regfile_wdata_lsu;
      rvfi_mem_wdata_d = data_wdata_ex;
    end else begin
      rvfi_mem_addr_d  = rvfi_mem_addr_q;
      rvfi_mem_rdata_d = rvfi_mem_rdata_q;
      rvfi_mem_wdata_d = rvfi_mem_wdata_q;
    end
  end
  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_mem_addr_q  <= '0;
      rvfi_mem_rdata_q <= '0;
      rvfi_mem_wdata_q <= '0;
    end else begin
      rvfi_mem_addr_q  <= rvfi_mem_addr_d;
      rvfi_mem_rdata_q <= rvfi_mem_rdata_d;
      rvfi_mem_wdata_q <= rvfi_mem_wdata_d;
    end
  end
  // Byte enable based on data type
  always_comb begin
    unique case (data_type_ex)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  always_comb begin
    if (instr_is_compressed_id) begin
      rvfi_insn_id = {16'b0, instr_rdata_c_id};
    end else begin
      rvfi_insn_id = instr_rdata_id;
    end
  end

  // Source register data are kept stable for each instruction cycle
  always_comb begin
    if (instr_new_id) begin
      rvfi_rs1_data_d = rvfi_rs1_data_id;
      rvfi_rs2_data_d = rvfi_rs2_data_id;
    end else begin
      rvfi_rs1_data_d = rvfi_rs1_data_q;
      rvfi_rs2_data_d = rvfi_rs2_data_q;
    end
  end
  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rs1_data_q <= '0;
      rvfi_rs2_data_q <= '0;
    end else begin
      rvfi_rs1_data_q <= rvfi_rs1_data_d;
      rvfi_rs2_data_q <= rvfi_rs2_data_d;
    end
  end

  // RD write register is refreshed only once per cycle and
  // then it is kept stable for the cycle.
  always_comb begin
    if (rvfi_insn_new_d) begin
      if (!rvfi_rd_we_id) begin
        rvfi_rd_addr_d    = '0;
        rvfi_rd_wdata_d   = '0;
      end else begin
        rvfi_rd_addr_d = rvfi_rd_addr_id;
        if (rvfi_rd_addr_id == 5'h0) begin
          rvfi_rd_wdata_d = '0;
        end else begin
          rvfi_rd_wdata_d = rvfi_rd_wdata_id;
        end
      end
    end else begin
      rvfi_rd_addr_d    = rvfi_rd_addr_q;
      rvfi_rd_wdata_d   = rvfi_rd_wdata_q;
    end
  end
  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rd_addr_q    <= '0;
      rvfi_rd_wdata_q   <= '0;
    end else begin
      rvfi_rd_addr_q    <= rvfi_rd_addr_d;
      rvfi_rd_wdata_q   <= rvfi_rd_wdata_d;
    end
  end

  always_comb begin
    if (instr_new_id) begin
      rvfi_insn_new_d = 1'b1;
    end else begin
      rvfi_insn_new_d = rvfi_insn_new_q;
    end
  end
  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_insn_new_q <= 1'b0;
    end else begin
      if (instr_ret) begin
        rvfi_insn_new_q <= 1'b0;
      end else begin
        rvfi_insn_new_q <= rvfi_insn_new_d;
      end
    end
  end

  // generate rvfi_intr_d
  assign rvfi_intr_d = rvfi_set_trap_pc_q & rvfi_insn_new_d;

  always_comb begin
    rvfi_set_trap_pc_d = rvfi_set_trap_pc_q;

    if (pc_set && pc_mux_id == PC_EXC &&
        (exc_pc_mux_id == EXC_PC_EXC || exc_pc_mux_id == EXC_PC_IRQ)) begin
      // PC is set to enter a trap handler
      rvfi_set_trap_pc_d = 1'b1;
    end else if (rvfi_set_trap_pc_q && instr_ret) begin
      // first instruction has been executed after PC is set to trap handler
      rvfi_set_trap_pc_d = 1'b0;
    end
  end

  always_ff @(posedge clk or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_set_trap_pc_q <= 1'b0;
    end else begin
      rvfi_set_trap_pc_q <= rvfi_set_trap_pc_d;
    end
  end

`endif

endmodule
