// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

/**
 * Instruction Decode Stage
 *
 * Decode stage of the core. It decodes the instructions and hosts the register
 * file.
 */
module ibex_id_stage #(
    parameter bit RV32E = 0,
    parameter bit RV32M = 1
) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    input  logic                  test_en_i,

    input  logic                  fetch_enable_i,
    output logic                  ctrl_busy_o,
    output logic                  illegal_insn_o,

    // Interface to IF stage
    input  logic                  instr_valid_i,
    input  logic                  instr_new_i,
    input  logic [31:0]           instr_rdata_i,         // from IF-ID pipeline registers
    input  logic [15:0]           instr_rdata_c_i,       // from IF-ID pipeline registers
    input  logic                  instr_is_compressed_i,
    output logic                  instr_req_o,
    output logic                  instr_valid_clear_o,   // kill instr in IF-ID reg
    output logic                  id_in_ready_o,         // ID stage is ready for next instr

    // Jumps and branches
    input  logic                  branch_decision_i,

    // IF and ID stage signals
    output logic                  pc_set_o,
    output ibex_pkg::pc_sel_e     pc_mux_o,
    output ibex_pkg::exc_pc_sel_e exc_pc_mux_o,
    output ibex_pkg::exc_cause_e  exc_cause_o,

    input  logic                  illegal_c_insn_i,
    input  logic                  instr_fetch_err_i,

    input  logic [31:0]           pc_id_i,

    // Stalls
    input  logic                  ex_valid_i,     // EX stage has valid output
    input  logic                  lsu_valid_i,    // LSU has valid output, or is done
    // ALU
    output ibex_pkg::alu_op_e     alu_operator_ex_o,
    output logic [31:0]           alu_operand_a_ex_o,
    output logic [31:0]           alu_operand_b_ex_o,

    // MUL, DIV
    output logic                  mult_en_ex_o,
    output logic                  div_en_ex_o,
    output ibex_pkg::md_op_e      multdiv_operator_ex_o,
    output logic  [1:0]           multdiv_signed_mode_ex_o,
    output logic [31:0]           multdiv_operand_a_ex_o,
    output logic [31:0]           multdiv_operand_b_ex_o,

    // CSR
    output logic                  csr_access_o,
    output ibex_pkg::csr_op_e     csr_op_o,
    output logic                  csr_save_if_o,
    output logic                  csr_save_id_o,
    output logic                  csr_restore_mret_id_o,
    output logic                  csr_restore_dret_id_o,
    output logic                  csr_save_cause_o,
    output logic [31:0]           csr_mtval_o,
    input  ibex_pkg::priv_lvl_e   priv_mode_i,
    input  logic                  csr_mstatus_tw_i,
    input  logic                  illegal_csr_insn_i,

    // Interface to load store unit
    output logic                  data_req_ex_o,
    output logic                  data_we_ex_o,
    output logic [1:0]            data_type_ex_o,
    output logic                  data_sign_ext_ex_o,
    output logic [31:0]           data_wdata_ex_o,

    input  logic                  lsu_addr_incr_req_i,
    input  logic [31:0]           lsu_addr_last_i,

    // Interrupt signals
    input  logic                  csr_mstatus_mie_i,
    input  logic                  csr_msip_i,
    input  logic                  csr_mtip_i,
    input  logic                  csr_meip_i,
    input  logic [14:0]           csr_mfip_i,
    input  logic                  irq_pending_i,
    input  logic                  irq_nm_i,

    input  logic                  lsu_load_err_i,
    input  logic                  lsu_store_err_i,

    // Debug Signal
    output logic                  debug_mode_o,
    output ibex_pkg::dbg_cause_e  debug_cause_o,
    output logic                  debug_csr_save_o,
    input  logic                  debug_req_i,
    input  logic                  debug_single_step_i,
    input  logic                  debug_ebreakm_i,
    input  logic                  debug_ebreaku_i,

    // Write back signal
    input  logic [31:0]           regfile_wdata_lsu_i,
    input  logic [31:0]           regfile_wdata_ex_i,
    input  logic [31:0]           csr_rdata_i,

`ifdef RVFI
    output logic [4:0]            rfvi_reg_raddr_ra_o,
    output logic [31:0]           rfvi_reg_rdata_ra_o,
    output logic [4:0]            rfvi_reg_raddr_rb_o,
    output logic [31:0]           rfvi_reg_rdata_rb_o,
    output logic [4:0]            rfvi_reg_waddr_rd_o,
    output logic [31:0]           rfvi_reg_wdata_rd_o,
    output logic                  rfvi_reg_we_o,
`endif

    // Performance Counters
    output logic                  perf_jump_o,    // executing a jump instr
    output logic                  perf_branch_o,  // executing a branch instr
    output logic                  perf_tbranch_o, // executing a taken branch instr
    output logic                  instr_ret_o,
    output logic                  instr_ret_compressed_o
);

  import ibex_pkg::*;

  // Decoder/Controller, ID stage internal signals
  logic        illegal_insn_dec;
  logic        ebrk_insn;
  logic        mret_insn_dec;
  logic        dret_insn_dec;
  logic        ecall_insn_dec;
  logic        wfi_insn_dec;

  logic        branch_in_dec;
  logic        branch_set_n, branch_set_q;
  logic        jump_in_dec;
  logic        jump_set;

  logic        instr_executing;
  logic        instr_multicycle;
  logic        instr_multicycle_done_n, instr_multicycle_done_q;
  logic        stall_lsu;
  logic        stall_multdiv;
  logic        stall_branch;
  logic        stall_jump;

  // Immediate decoding and sign extension
  logic [31:0] imm_i_type;
  logic [31:0] imm_s_type;
  logic [31:0] imm_b_type;
  logic [31:0] imm_u_type;
  logic [31:0] imm_j_type;
  logic [31:0] zimm_rs1_type;

  logic [31:0] imm_a;       // contains the immediate for operand b
  logic [31:0] imm_b;       // contains the immediate for operand b

  // Register file interface
  logic [4:0]  regfile_raddr_a;
  logic [4:0]  regfile_raddr_b;

  logic [4:0]  regfile_waddr;

  logic [31:0] regfile_rdata_a;
  logic [31:0] regfile_rdata_b;
  logic [31:0] regfile_wdata;

  rf_wd_sel_e  regfile_wdata_sel;
  logic        regfile_we;
  logic        regfile_we_wb, regfile_we_dec;

  // ALU Control
  alu_op_e     alu_operator;
  op_a_sel_e   alu_op_a_mux_sel, alu_op_a_mux_sel_dec;
  op_b_sel_e   alu_op_b_mux_sel, alu_op_b_mux_sel_dec;

  imm_a_sel_e  imm_a_mux_sel;
  imm_b_sel_e  imm_b_mux_sel, imm_b_mux_sel_dec;

  // Multiplier Control
  logic        mult_en_id, mult_en_dec; // use integer multiplier
  logic        div_en_id, div_en_dec;   // use integer division or reminder
  logic        multdiv_en_dec;
  md_op_e      multdiv_operator;
  logic [1:0]  multdiv_signed_mode;

  // Data Memory Control
  logic        data_we_id;
  logic [1:0]  data_type_id;
  logic        data_sign_ext_id;
  logic        data_req_id, data_req_dec;

  // CSR control
  logic        csr_pipe_flush;

  logic [31:0] alu_operand_a;
  logic [31:0] alu_operand_b;

  /////////////
  // LSU Mux //
  /////////////

  // Misaligned loads/stores result in two aligned loads/stores, compute second address
  assign alu_op_a_mux_sel = lsu_addr_incr_req_i ? OP_A_FWD        : alu_op_a_mux_sel_dec;
  assign alu_op_b_mux_sel = lsu_addr_incr_req_i ? OP_B_IMM        : alu_op_b_mux_sel_dec;
  assign imm_b_mux_sel    = lsu_addr_incr_req_i ? IMM_B_INCR_ADDR : imm_b_mux_sel_dec;

  ///////////////////
  // Operand A MUX //
  ///////////////////

  // Immediate MUX for Operand A
  assign imm_a = (imm_a_mux_sel == IMM_A_Z) ? zimm_rs1_type : '0;

  // ALU MUX for Operand A
  always_comb begin : alu_operand_a_mux
    unique case (alu_op_a_mux_sel)
      OP_A_REG_A:  alu_operand_a = regfile_rdata_a;
      OP_A_FWD:    alu_operand_a = lsu_addr_last_i;
      OP_A_CURRPC: alu_operand_a = pc_id_i;
      OP_A_IMM:    alu_operand_a = imm_a;
      default:     alu_operand_a = 'X;
    endcase
  end

  ///////////////////
  // Operand B MUX //
  ///////////////////

  // Immediate MUX for Operand B
  always_comb begin : immediate_b_mux
    unique case (imm_b_mux_sel)
      IMM_B_I:         imm_b = imm_i_type;
      IMM_B_S:         imm_b = imm_s_type;
      IMM_B_B:         imm_b = imm_b_type;
      IMM_B_U:         imm_b = imm_u_type;
      IMM_B_J:         imm_b = imm_j_type;
      IMM_B_INCR_PC:   imm_b = instr_is_compressed_i ? 32'h2 : 32'h4;
      IMM_B_INCR_ADDR: imm_b = 32'h4;
      default:         imm_b = 'X;
    endcase
  end

  // ALU MUX for Operand B
  assign alu_operand_b = (alu_op_b_mux_sel == OP_B_IMM) ? imm_b : regfile_rdata_b;

  ///////////////////////
  // Register File MUX //
  ///////////////////////

  // Register file write enable mux - do not propagate illegal CSR ops, do not write when idle,
  // for loads/stores and multdiv operations write when the data is ready only
  assign regfile_we = (illegal_csr_insn_i || !instr_executing) ? 1'b0          :
                      (data_req_dec || multdiv_en_dec)         ? regfile_we_wb : regfile_we_dec;

  // Register file write data mux
  always_comb begin : regfile_wdata_mux
    unique case (regfile_wdata_sel)
      RF_WD_EX:  regfile_wdata = regfile_wdata_ex_i;
      RF_WD_LSU: regfile_wdata = regfile_wdata_lsu_i;
      RF_WD_CSR: regfile_wdata = csr_rdata_i;
      default:   regfile_wdata = 'X;
    endcase;
  end

  ///////////////////
  // Register File //
  ///////////////////

  ibex_register_file #( .RV32E ( RV32E ) ) registers_i (
      .clk_i        ( clk_i           ),
      .rst_ni       ( rst_ni          ),

      .test_en_i    ( test_en_i       ),

      // Read port a
      .raddr_a_i    ( regfile_raddr_a ),
      .rdata_a_o    ( regfile_rdata_a ),
      // Read port b
      .raddr_b_i    ( regfile_raddr_b ),
      .rdata_b_o    ( regfile_rdata_b ),
      // write port
      .waddr_a_i    ( regfile_waddr   ),
      .wdata_a_i    ( regfile_wdata   ),
      .we_a_i       ( regfile_we      )
  );

`ifdef RVFI
  assign rfvi_reg_raddr_ra_o = regfile_raddr_a;
  assign rfvi_reg_rdata_ra_o = regfile_rdata_a;
  assign rfvi_reg_raddr_rb_o = regfile_raddr_b;
  assign rfvi_reg_rdata_rb_o = regfile_rdata_b;
  assign rfvi_reg_waddr_rd_o = regfile_waddr;
  assign rfvi_reg_wdata_rd_o = regfile_wdata;
  assign rfvi_reg_we_o       = regfile_we;
`endif

  /////////////
  // Decoder //
  /////////////

  ibex_decoder #(
      .RV32E ( RV32E ),
      .RV32M ( RV32M )
  ) decoder_i (
      // controller
      .illegal_insn_o                  ( illegal_insn_dec     ),
      .ebrk_insn_o                     ( ebrk_insn            ),
      .mret_insn_o                     ( mret_insn_dec        ),
      .dret_insn_o                     ( dret_insn_dec        ),
      .ecall_insn_o                    ( ecall_insn_dec       ),
      .wfi_insn_o                      ( wfi_insn_dec         ),
      .jump_set_o                      ( jump_set             ),

      // from IF-ID pipeline register
      .instr_new_i                     ( instr_new_i          ),
      .instr_rdata_i                   ( instr_rdata_i        ),
      .illegal_c_insn_i                ( illegal_c_insn_i     ),

      // immediates
      .imm_a_mux_sel_o                 ( imm_a_mux_sel        ),
      .imm_b_mux_sel_o                 ( imm_b_mux_sel_dec    ),

      .imm_i_type_o                    ( imm_i_type           ),
      .imm_s_type_o                    ( imm_s_type           ),
      .imm_b_type_o                    ( imm_b_type           ),
      .imm_u_type_o                    ( imm_u_type           ),
      .imm_j_type_o                    ( imm_j_type           ),
      .zimm_rs1_type_o                 ( zimm_rs1_type        ),

      // register file
      .regfile_wdata_sel_o             ( regfile_wdata_sel    ),
      .regfile_we_o                    ( regfile_we_dec       ),

      .regfile_raddr_a_o               ( regfile_raddr_a      ),
      .regfile_raddr_b_o               ( regfile_raddr_b      ),
      .regfile_waddr_o                 ( regfile_waddr        ),

      // ALU
      .alu_operator_o                  ( alu_operator         ),
      .alu_op_a_mux_sel_o              ( alu_op_a_mux_sel_dec ),
      .alu_op_b_mux_sel_o              ( alu_op_b_mux_sel_dec ),

      // MULT & DIV
      .mult_en_o                       ( mult_en_dec          ),
      .div_en_o                        ( div_en_dec           ),
      .multdiv_operator_o              ( multdiv_operator     ),
      .multdiv_signed_mode_o           ( multdiv_signed_mode  ),

      // CSRs
      .csr_access_o                    ( csr_access_o         ),
      .csr_op_o                        ( csr_op_o             ),
      .csr_pipe_flush_o                ( csr_pipe_flush       ),

      // LSU
      .data_req_o                      ( data_req_dec         ),
      .data_we_o                       ( data_we_id           ),
      .data_type_o                     ( data_type_id         ),
      .data_sign_extension_o           ( data_sign_ext_id     ),

      // jump/branches
      .jump_in_dec_o                   ( jump_in_dec          ),
      .branch_in_dec_o                 ( branch_in_dec        )
  );

  ////////////////
  // Controller //
  ////////////////

  assign illegal_insn_o = instr_valid_i & (illegal_insn_dec | illegal_csr_insn_i);

  ibex_controller controller_i (
      .clk_i                          ( clk_i                  ),
      .rst_ni                         ( rst_ni                 ),

      .fetch_enable_i                 ( fetch_enable_i         ),
      .ctrl_busy_o                    ( ctrl_busy_o            ),

      // decoder related signals
      .illegal_insn_i                 ( illegal_insn_o         ),
      .ecall_insn_i                   ( ecall_insn_dec         ),
      .mret_insn_i                    ( mret_insn_dec          ),
      .dret_insn_i                    ( dret_insn_dec          ),
      .wfi_insn_i                     ( wfi_insn_dec           ),
      .ebrk_insn_i                    ( ebrk_insn              ),
      .csr_pipe_flush_i               ( csr_pipe_flush         ),

      // from IF-ID pipeline
      .instr_valid_i                  ( instr_valid_i          ),
      .instr_i                        ( instr_rdata_i          ),
      .instr_compressed_i             ( instr_rdata_c_i        ),
      .instr_is_compressed_i          ( instr_is_compressed_i  ),
      .instr_fetch_err_i              ( instr_fetch_err_i      ),
      .pc_id_i                        ( pc_id_i                ),

      // to IF-ID pipeline
      .instr_valid_clear_o            ( instr_valid_clear_o    ),
      .id_in_ready_o                  ( id_in_ready_o          ),

      // to prefetcher
      .instr_req_o                    ( instr_req_o            ),
      .pc_set_o                       ( pc_set_o               ),
      .pc_mux_o                       ( pc_mux_o               ),
      .exc_pc_mux_o                   ( exc_pc_mux_o           ),
      .exc_cause_o                    ( exc_cause_o            ),

      // LSU
      .lsu_addr_last_i                ( lsu_addr_last_i        ),
      .load_err_i                     ( lsu_load_err_i         ),
      .store_err_i                    ( lsu_store_err_i        ),

      // jump/branch control
      .branch_set_i                   ( branch_set_q           ),
      .jump_set_i                     ( jump_set               ),

      // interrupt signals
      .csr_mstatus_mie_i              ( csr_mstatus_mie_i      ),
      .csr_msip_i                     ( csr_msip_i             ),
      .csr_mtip_i                     ( csr_mtip_i             ),
      .csr_meip_i                     ( csr_meip_i             ),
      .csr_mfip_i                     ( csr_mfip_i             ),
      .irq_pending_i                  ( irq_pending_i          ),
      .irq_nm_i                       ( irq_nm_i               ),

      // CSR Controller Signals
      .csr_save_if_o                  ( csr_save_if_o          ),
      .csr_save_id_o                  ( csr_save_id_o          ),
      .csr_restore_mret_id_o          ( csr_restore_mret_id_o  ),
      .csr_restore_dret_id_o          ( csr_restore_dret_id_o  ),
      .csr_save_cause_o               ( csr_save_cause_o       ),
      .csr_mtval_o                    ( csr_mtval_o            ),
      .priv_mode_i                    ( priv_mode_i            ),
      .csr_mstatus_tw_i               ( csr_mstatus_tw_i       ),

      // Debug Signal
      .debug_mode_o                   ( debug_mode_o           ),
      .debug_cause_o                  ( debug_cause_o          ),
      .debug_csr_save_o               ( debug_csr_save_o       ),
      .debug_req_i                    ( debug_req_i            ),
      .debug_single_step_i            ( debug_single_step_i    ),
      .debug_ebreakm_i                ( debug_ebreakm_i        ),
      .debug_ebreaku_i                ( debug_ebreaku_i        ),

      // stall signals
      .stall_lsu_i                    ( stall_lsu              ),
      .stall_multdiv_i                ( stall_multdiv          ),
      .stall_jump_i                   ( stall_jump             ),
      .stall_branch_i                 ( stall_branch           ),

      // Performance Counters
      .perf_jump_o                    ( perf_jump_o            ),
      .perf_tbranch_o                 ( perf_tbranch_o         )
  );

  //////////////
  // ID-EX/WB //
  //////////////

  assign multdiv_en_dec   = mult_en_dec | div_en_dec;
  assign instr_multicycle = data_req_dec | multdiv_en_dec | branch_in_dec | jump_in_dec;

  // Forward decoder output to EX, WB and controller only if current instr is still
  // being executed. This is the case if the current instr is either:
  // - a new instr (not yet done)
  // - a multicycle instr that is not yet done
  // An instruction error will suppress any requests or register writes
  assign instr_executing = (instr_new_i | (instr_multicycle & ~instr_multicycle_done_q)) &
                           ~instr_fetch_err_i;
  assign data_req_id     = instr_executing ? data_req_dec  : 1'b0;
  assign mult_en_id      = instr_executing ? mult_en_dec   : 1'b0;
  assign div_en_id       = instr_executing ? div_en_dec    : 1'b0;

  ///////////
  // ID-EX //
  ///////////

  assign data_req_ex_o               = data_req_id;
  assign data_we_ex_o                = data_we_id;
  assign data_type_ex_o              = data_type_id;
  assign data_sign_ext_ex_o          = data_sign_ext_id;
  assign data_wdata_ex_o             = regfile_rdata_b;

  assign alu_operator_ex_o           = alu_operator;
  assign alu_operand_a_ex_o          = alu_operand_a;
  assign alu_operand_b_ex_o          = alu_operand_b;

  assign mult_en_ex_o                = mult_en_id;
  assign div_en_ex_o                 = div_en_id;

  assign multdiv_operator_ex_o       = multdiv_operator;
  assign multdiv_signed_mode_ex_o    = multdiv_signed_mode;
  assign multdiv_operand_a_ex_o      = regfile_rdata_a;
  assign multdiv_operand_b_ex_o      = regfile_rdata_b;

  typedef enum logic { IDLE, WAIT_MULTICYCLE } id_fsm_e;
  id_fsm_e id_wb_fsm_cs, id_wb_fsm_ns;

  ////////////////////////////////
  // ID-EX/WB Pipeline Register //
  ////////////////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : id_wb_pipeline_reg
    if (!rst_ni) begin
      id_wb_fsm_cs            <= IDLE;
      branch_set_q            <= 1'b0;
      instr_multicycle_done_q <= 1'b0;
    end else begin
      id_wb_fsm_cs            <= id_wb_fsm_ns;
      branch_set_q            <= branch_set_n;
      instr_multicycle_done_q <= instr_multicycle_done_n;
    end
  end

  //////////////////
  // ID-EX/WB FSM //
  //////////////////

  always_comb begin : id_wb_fsm
    id_wb_fsm_ns            = id_wb_fsm_cs;
    instr_multicycle_done_n = instr_multicycle_done_q;
    regfile_we_wb           = 1'b0;
    stall_lsu               = 1'b0;
    stall_multdiv           = 1'b0;
    stall_jump              = 1'b0;
    stall_branch            = 1'b0;
    branch_set_n            = 1'b0;
    perf_branch_o           = 1'b0;
    instr_ret_o             = 1'b0;

    unique case (id_wb_fsm_cs)

      IDLE: begin
        // only detect multicycle when instruction is new, do not re-detect after
        // execution (when waiting for next instruction from IF stage)
        if (instr_new_i & ~instr_fetch_err_i) begin
          unique case (1'b1)
            data_req_dec: begin
              // LSU operation
              id_wb_fsm_ns            = WAIT_MULTICYCLE;
              stall_lsu               = 1'b1;
              instr_multicycle_done_n = 1'b0;
            end
            multdiv_en_dec: begin
              // MUL or DIV operation
              id_wb_fsm_ns            = WAIT_MULTICYCLE;
              stall_multdiv           = 1'b1;
              instr_multicycle_done_n = 1'b0;
            end
            branch_in_dec: begin
              // cond branch operation
              id_wb_fsm_ns            =  branch_decision_i ? WAIT_MULTICYCLE : IDLE;
              stall_branch            =  branch_decision_i;
              instr_multicycle_done_n = ~branch_decision_i;
              branch_set_n            =  branch_decision_i;
              perf_branch_o           =  1'b1;
              instr_ret_o             = ~branch_decision_i;
            end
            jump_in_dec: begin
              // uncond branch operation
              id_wb_fsm_ns            = WAIT_MULTICYCLE;
              stall_jump              = 1'b1;
              instr_multicycle_done_n = 1'b0;
            end
            default: begin
              instr_multicycle_done_n = 1'b0;
              instr_ret_o             = 1'b1;
            end
          endcase
        end
      end

      WAIT_MULTICYCLE: begin
        if ((data_req_dec & lsu_valid_i) | (~data_req_dec & ex_valid_i)) begin
          id_wb_fsm_ns            = IDLE;
          instr_multicycle_done_n = 1'b1;
          regfile_we_wb           = regfile_we_dec & ~lsu_load_err_i;
          instr_ret_o             = 1'b1;
        end else begin
          stall_lsu               = data_req_dec;
          stall_multdiv           = multdiv_en_dec;
          stall_branch            = branch_in_dec;
          stall_jump              = jump_in_dec;
        end
      end

      default: begin
        id_wb_fsm_ns = id_fsm_e'(1'bX);
      end
    endcase
  end

  assign instr_ret_compressed_o = instr_ret_o & instr_is_compressed_i;

  ////////////////
  // Assertions //
  ////////////////

`ifndef VERILATOR
  // branch decision must be valid when jumping
  assert property (@(posedge clk_i) disable iff (!rst_ni)
      (branch_decision_i !== 1'bx || !branch_in_dec)) else
    $display("Branch decision is X");

`ifdef CHECK_MISALIGNED
  assert property (@(posedge clk_i) disable iff (!rst_ni)
      (!lsu_addr_incr_req_i)) else
    $display("Misaligned memory access at %x",pc_id_i);
`endif

  // instruction delivered to ID stage must always be valid
  assert property (@(posedge clk_i) disable iff (!rst_ni)
      (instr_valid_i && !(illegal_c_insn_i || instr_fetch_err_i)) |->
      (!$isunknown(instr_rdata_i))) else
    $display("Instruction is valid, but has at least one X");

  // multicycle enable signals must be unique
  assert property (@(posedge clk_i) disable iff (!rst_ni)
      ($onehot0({data_req_dec, multdiv_en_dec, branch_in_dec, jump_in_dec}))) else
    $display("Multicycle enable signals are not unique");
`endif

endmodule
