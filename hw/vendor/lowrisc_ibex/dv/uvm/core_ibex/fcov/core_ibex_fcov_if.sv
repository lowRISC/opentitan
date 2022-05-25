// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
`include "core_ibex_csr_categories.svh"

interface core_ibex_fcov_if import ibex_pkg::*; (
  input clk_i,
  input rst_ni,

  input priv_lvl_e priv_mode_id,
  input priv_lvl_e priv_mode_lsu,

  input debug_mode,

  input fcov_csr_read_only,
  input fcov_csr_write
);
  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;

  typedef enum {
    InstrCategoryALU,
    InstrCategoryMul,
    InstrCategoryDiv,
    InstrCategoryBranch,
    InstrCategoryJump,
    InstrCategoryLoad,
    InstrCategoryStore,
    InstrCategoryCSRAccess,
    InstrCategoryEBreakDbg,
    InstrCategoryEBreakExc,
    InstrCategoryECall,
    InstrCategoryMRet,
    InstrCategoryDRet,
    InstrCategoryWFI,
    InstrCategoryFence,
    InstrCategoryFenceI,
    InstrCategoryNone,
    InstrCategoryFetchError,
    InstrCategoryCompressedIllegal,
    InstrCategoryUncompressedIllegal,
    InstrCategoryCSRIllegal,
    InstrCategoryPrivIllegal,
    InstrCategoryOtherIllegal,
    // Category not in coverage plan, it should never be seen. An instruction given the Other
    // category should either be classified under an existing category or a new category should be
    // created as appropriate.
    InstrCategoryOther
  } instr_category_e;

  typedef enum {
    IdStallTypeNone,
    IdStallTypeInstr,
    IdStallTypeLdHz,
    IdStallTypeMem
  } id_stall_type_e;

  instr_category_e id_instr_category;
  // Set `id_instr_category` to the appropriate category for the uncompressed instruction in the
  // ID/EX stage.  Compressed instructions are not handled (`id_stage_i.instr_rdata_i` is always
  // uncompressed).  When the `id_stage.instr_valid_i` isn't set `InstrCategoryNone` is the given
  // instruction category.
  always_comb begin
    id_instr_category = InstrCategoryOther;

    case (id_stage_i.instr_rdata_i[6:0])
      ibex_pkg::OPCODE_LUI:    id_instr_category = InstrCategoryALU;
      ibex_pkg::OPCODE_AUIPC:  id_instr_category = InstrCategoryALU;
      ibex_pkg::OPCODE_JAL:    id_instr_category = InstrCategoryJump;
      ibex_pkg::OPCODE_JALR:   id_instr_category = InstrCategoryJump;
      ibex_pkg::OPCODE_BRANCH: id_instr_category = InstrCategoryBranch;
      ibex_pkg::OPCODE_LOAD:   id_instr_category = InstrCategoryLoad;
      ibex_pkg::OPCODE_STORE:  id_instr_category = InstrCategoryStore;
      ibex_pkg::OPCODE_OP_IMM: id_instr_category = InstrCategoryALU;
      ibex_pkg::OPCODE_OP: begin
        if ({id_stage_i.instr_rdata_i[26], id_stage_i.instr_rdata_i[13:12]} == {1'b1, 2'b01}) begin
          id_instr_category = InstrCategoryALU; // reg-reg/reg-imm ops
        end else if (id_stage_i.instr_rdata_i[31:25] inside {7'b000_0000, 7'b010_0000, 7'b011_0000,
              7'b011_0100, 7'b001_0100, 7'b001_0000, 7'b000_0101, 7'b000_0100, 7'b010_0100}) begin
          id_instr_category = InstrCategoryALU; // RV32I and RV32B reg-reg/reg-imm ops
        end else if (id_stage_i.instr_rdata_i[31:25] == 7'b000_0001) begin
          if (id_stage_i.instr_rdata_i[14]) begin
            id_instr_category = InstrCategoryDiv; // DIV*
          end else begin
            id_instr_category = InstrCategoryMul; // MUL*
          end
        end
      end
      ibex_pkg::OPCODE_SYSTEM: begin
        if (id_stage_i.instr_rdata_i[14:12] == 3'b000) begin
          case (id_stage_i.instr_rdata_i[31:20])
            12'h000: id_instr_category = InstrCategoryECall;
            12'h001: begin
              if (id_stage_i.debug_ebreakm_i && priv_mode_id == PRIV_LVL_M) begin
                id_instr_category = InstrCategoryEBreakDbg;
              end else if (id_stage_i.debug_ebreaku_i && priv_mode_id == PRIV_LVL_U) begin
                id_instr_category = InstrCategoryEBreakDbg;
              end else begin
                id_instr_category = InstrCategoryEBreakExc;
              end
            end
            12'h302: id_instr_category = InstrCategoryMRet;
            12'h7b2: id_instr_category = InstrCategoryDRet;
            12'h105: id_instr_category = InstrCategoryWFI;
          endcase
        end else begin
          id_instr_category = InstrCategoryCSRAccess;
        end
      end
      ibex_pkg::OPCODE_MISC_MEM: begin
        case (id_stage_i.instr_rdata_i[14:12])
          3'b000: id_instr_category = InstrCategoryFence;
          3'b001: id_instr_category = InstrCategoryFenceI;
        endcase
      end
      default: id_instr_category = InstrCategoryOther;
    endcase

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.instr_fetch_err_i) begin
        id_instr_category = InstrCategoryFetchError;
      end else if (id_stage_i.illegal_c_insn_i) begin
        id_instr_category = InstrCategoryCompressedIllegal;
      end else if (id_stage_i.illegal_insn_dec) begin
        id_instr_category = InstrCategoryUncompressedIllegal;
      end else if (id_stage_i.illegal_csr_insn_i) begin
        if (cs_registers_i.illegal_csr_priv || cs_registers_i.illegal_csr_dbg) begin
          id_instr_category = InstrCategoryPrivIllegal;
        end else begin
          id_instr_category = InstrCategoryCSRIllegal;
        end
      end else if (id_stage_i.illegal_insn_o) begin
        if (id_stage_i.illegal_dret_insn || id_stage_i.illegal_umode_insn) begin
          id_instr_category = InstrCategoryPrivIllegal;
        end else begin
          id_instr_category = InstrCategoryOtherIllegal;
        end
      end
    end else begin
      id_instr_category = InstrCategoryNone;
    end
  end

  // Check instruction categories calculated from instruction bits match what decoder has produced.

  // The ALU category is tricky as there's no specific ALU enable and instructions that actively use
  // the result of the ALU but aren't themselves ALU operations (such as load/store and JALR). This
  // categorizes anything that selects the ALU as the source of register write data and enables
  // register writes minus some exclusions as an ALU operation.
  `ASSERT(InstrCategoryALUCorrect, id_instr_category == InstrCategoryALU |->
      (id_stage_i.rf_wdata_sel == RF_WD_EX) && id_stage_i.rf_we_dec && ~id_stage_i.mult_sel_ex_o &&
      ~id_stage_i.div_sel_ex_o && ~id_stage_i.lsu_req_dec && ~id_stage_i.jump_in_dec);

  `ASSERT(InstrCategoryMulCorrect,
      id_instr_category == InstrCategoryMul |-> id_stage_i.mult_sel_ex_o)

  `ASSERT(InstrCategoryDivCorrect,
      id_instr_category == InstrCategoryDiv |-> id_stage_i.div_sel_ex_o)

  `ASSERT(InstrCategoryBranchCorrect,
      id_instr_category == InstrCategoryBranch |-> id_stage_i.branch_in_dec)

  `ASSERT(InstrCategoryJumpCorrect,
      id_instr_category == InstrCategoryJump |-> id_stage_i.jump_in_dec)

  `ASSERT(InstrCategoryLoadCorrect,
      id_instr_category == InstrCategoryLoad |-> id_stage_i.lsu_req_dec && !id_stage_i.lsu_we)

  `ASSERT(InstrCategoryStoreCorrect,
      id_instr_category == InstrCategoryStore |-> id_stage_i.lsu_req_dec && id_stage_i.lsu_we)

  `ASSERT(InstrCategoryCSRAccessCorrect,
      id_instr_category == InstrCategoryCSRAccess |-> id_stage_i.csr_access_o)
  `ASSERT(InstrCategoryEBreakDbgCorrect, id_instr_category == InstrCategoryEBreakDbg |->
      id_stage_i.ebrk_insn && id_stage_i.controller_i.ebreak_into_debug)

  `ASSERT(InstrCategoryEBreakExcCorrect, id_instr_category == InstrCategoryEBreakExc |->
      id_stage_i.ebrk_insn && !id_stage_i.controller_i.ebreak_into_debug)

  `ASSERT(InstrCategoryECallCorrect,
      id_instr_category == InstrCategoryECall |-> id_stage_i.ecall_insn_dec)

  `ASSERT(InstrCategoryMRetCorrect,
      id_instr_category == InstrCategoryMRet |-> id_stage_i.mret_insn_dec)

  `ASSERT(InstrCategoryDRetCorrect,
      id_instr_category == InstrCategoryDRet |-> id_stage_i.dret_insn_dec)

  `ASSERT(InstrCategoryWFICorrect,
      id_instr_category == InstrCategoryWFI |-> id_stage_i.wfi_insn_dec)

  `ASSERT(InstrCategoryFenceICorrect,
      id_instr_category == InstrCategoryFenceI && id_stage_i.instr_first_cycle |->
      id_stage_i.icache_inval_o)



  id_stall_type_e id_stall_type;

  // Set `id_stall_type` to the appropriate type based on signals in the ID/EX stage
  always_comb begin
    id_stall_type = IdStallTypeNone;

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.stall_mem) begin
        id_stall_type = IdStallTypeMem;
      end

      if (id_stage_i.stall_ld_hz) begin
        id_stall_type = IdStallTypeLdHz;
      end

      if (id_stage_i.stall_multdiv || id_stage_i.stall_branch ||
          id_stage_i.stall_jump) begin
        id_stall_type = IdStallTypeInstr;
      end
    end
  end

  // IF specific state enum
  typedef enum {
    IFStageFullAndFetching,
    IFStageFullAndIdle,
    IFStageEmptyAndFetching,
    IFStageEmptyAndIdle
  } if_stage_state_e;

  // ID/EX and WB have the same state enum
  typedef enum {
    PipeStageFullAndStalled,
    PipeStageFullAndUnstalled,
    PipeStageEmpty
  } pipe_stage_state_e;

  if_stage_state_e   if_stage_state;
  pipe_stage_state_e id_stage_state;
  pipe_stage_state_e wb_stage_state;

  always_comb begin
    if_stage_state = IFStageEmptyAndIdle;

    if (if_stage_i.if_instr_valid) begin
      if (if_stage_i.req_i) begin
        if_stage_state = IFStageFullAndFetching;
      end else begin
        if_stage_state = IFStageFullAndIdle;
      end
    end else if(if_stage_i.req_i) begin
      if_stage_state = IFStageEmptyAndFetching;
    end
  end

  always_comb begin
    id_stage_state = PipeStageEmpty;

    if (id_stage_i.instr_valid_i) begin
      if (id_stage_i.id_in_ready_o) begin
        id_stage_state = PipeStageFullAndUnstalled;
      end else begin
        id_stage_state = PipeStageFullAndStalled;
      end
    end
  end

  always_comb begin
    wb_stage_state = PipeStageEmpty;

    if (wb_stage_i.fcov_wb_valid) begin
      if (wb_stage_i.ready_wb_o) begin
        wb_stage_state = PipeStageFullAndUnstalled;
      end else begin
        wb_stage_state = PipeStageFullAndStalled;
      end
    end
  end

  logic            instr_unstalled;
  logic            instr_unstalled_last;
  logic            id_stall_type_last_valid;
  id_stall_type_e  id_stall_type_last;
  instr_category_e id_instr_category_last;

  // Keep track of previous values for some signals. These are used for some of the crosses relating
  // to exception and debug entry. We want to cross different instruction categories and stalling
  // behaviour with exception and debug entry but signals indicating entry occur a cycle after the
  // relevant information is flushed from the pipeline.
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // First cycle out of reset there is no last stall, use valid bit to deal with this case
      id_stall_type_last_valid <= 1'b0;
      id_stall_type_last       <= IdStallTypeNone;
      instr_unstalled_last     <= 1'b0;
      id_instr_category_last   <= InstrCategoryNone;
    end else begin
      id_stall_type_last_valid <= 1'b1;
      id_stall_type_last       <= id_stall_type;
      instr_unstalled_last     <= instr_unstalled;
      id_instr_category_last   <= id_instr_category;
    end
  end

  assign instr_unstalled =
    (id_stall_type == IdStallTypeNone) && (id_stall_type_last != IdStallTypeNone) &&
    id_stall_type_last_valid;

  covergroup uarch_cg @(posedge clk_i);
    option.per_instance = 1;
    option.name = "uarch_cg";

    cp_id_instr_category: coverpoint id_instr_category {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    cp_id_instr_category_last: coverpoint id_instr_category_last {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    cp_stall_type_id: coverpoint id_stall_type;

    cp_wb_reg_no_load_hz: coverpoint id_stage_i.fcov_rf_rd_wb_hz &&
                                     !wb_stage_i.outstanding_load_wb_o;

    cp_ls_error_exception: coverpoint load_store_unit_i.fcov_ls_error_exception;
    cp_ls_pmp_exception: coverpoint load_store_unit_i.fcov_ls_pmp_exception;

    cp_branch_taken: coverpoint id_stage_i.fcov_branch_taken;
    cp_branch_not_taken: coverpoint id_stage_i.fcov_branch_not_taken;

    cp_priv_mode_id: coverpoint priv_mode_id {
      illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
    }
    cp_priv_mode_lsu: coverpoint priv_mode_lsu {
      illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
    }

    cp_if_stage_state : coverpoint if_stage_state;
    cp_id_stage_state : coverpoint id_stage_state;
    cp_wb_stage_state : coverpoint wb_stage_state;

    // TODO: MRET/WFI in debug mode?
    // Specific cover points for these as `id_instr_category` will be InstrCategoryPrivIllegal when
    // executing these instructions in U-mode.
    `DV_FCOV_EXPR_SEEN(mret_in_umode, id_stage_i.mret_insn_dec && priv_mode_id == PRIV_LVL_U)
    `DV_FCOV_EXPR_SEEN(wfi_in_umode, id_stage_i.wfi_insn_dec && priv_mode_id == PRIV_LVL_U)

    cp_irq_pending: coverpoint id_stage_i.irq_pending_i | id_stage_i.irq_nm_i;
    cp_debug_req: coverpoint id_stage_i.controller_i.fcov_debug_req;

    cp_csr_read_only: coverpoint cs_registers_i.csr_addr_i iff (fcov_csr_read_only) {
      ignore_bins ignore = {`IGNORED_CSRS};
    }

    cp_csr_write: coverpoint cs_registers_i.csr_addr_i iff (fcov_csr_write) {
      ignore_bins ignore = {`IGNORED_CSRS};
    }

    `DV_FCOV_EXPR_SEEN(csr_invalid_read_only, fcov_csr_read_only && cs_registers_i.illegal_csr)
    `DV_FCOV_EXPR_SEEN(csr_invalid_write, fcov_csr_write && cs_registers_i.illegal_csr)

    cp_debug_mode: coverpoint debug_mode;

    `DV_FCOV_EXPR_SEEN(interrupt_taken, id_stage_i.controller_i.fcov_interrupt_taken)
    `DV_FCOV_EXPR_SEEN(debug_entry_if, id_stage_i.controller_i.fcov_debug_entry_if)
    `DV_FCOV_EXPR_SEEN(debug_entry_id, id_stage_i.controller_i.fcov_debug_entry_id)
    `DV_FCOV_EXPR_SEEN(pipe_flush, id_stage_i.controller_i.fcov_pipe_flush)

    cp_controller_fsm: coverpoint id_stage_i.controller_i.ctrl_fsm_cs {
      bins out_of_reset = (RESET => BOOT_SET);
      bins out_of_boot_set = (BOOT_SET => FIRST_FETCH);
      bins out_of_first_fetch[] = (FIRST_FETCH => DECODE, IRQ_TAKEN, DBG_TAKEN_IF);
      bins out_of_decode[] = (DECODE => FLUSH, DBG_TAKEN_IF, IRQ_TAKEN);
      bins out_of_irq_taken = (IRQ_TAKEN => DECODE);
      bins out_of_debug_taken_if = (DBG_TAKEN_IF => DECODE);
      bins out_of_debug_taken_id = (DBG_TAKEN_ID => DECODE);
      bins out_of_flush[] = (FLUSH => DECODE, DBG_TAKEN_ID, WAIT_SLEEP, IRQ_TAKEN, DBG_TAKEN_IF);
      bins out_of_wait_sleep = (WAIT_SLEEP => SLEEP);
      bins out_of_sleep = (SLEEP => FIRST_FETCH);
      // TODO: VCS does not implement default sequence so illegal_bins will be empty
      illegal_bins illegal_transitions = default sequence;
    }

    priv_mode_instr_cross: cross cp_priv_mode_id, cp_id_instr_category;

    stall_cross: cross cp_id_instr_category, cp_stall_type_id {
      illegal_bins illegal =
        // Only Div, Mul, Branch and Jump instructions can see an instruction stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryDiv, InstrCategoryMul,
                                                 InstrCategoryBranch, InstrCategoryJump} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeInstr})
    ||
        // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSR Access can see a load hazard stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryALU, InstrCategoryMul,
                                                 InstrCategoryDiv, InstrCategoryBranch,
                                                 InstrCategoryJump, InstrCategoryLoad,
                                                 InstrCategoryStore, InstrCategoryCSRAccess} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeLdHz});
    }

    wb_reg_no_load_hz_instr_cross: cross cp_id_instr_category, cp_wb_reg_no_load_hz {
      // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSRAccess instructions can see a WB
      // register hazard
      illegal_bins illegal =
        !binsof(cp_id_instr_category) intersect {InstrCategoryALU, InstrCategoryMul,
          InstrCategoryDiv, InstrCategoryBranch, InstrCategoryJump, InstrCategoryLoad,
          InstrCategoryStore, InstrCategoryCSRAccess}                                  &&
        binsof(cp_wb_reg_no_load_hz) intersect {1'b1};
    }

    pipe_cross: cross cp_id_instr_category, cp_if_stage_state, cp_id_stage_state, wb_stage_state {
      // When ID stage is empty instruction category must be none
      illegal_bins illegal = !binsof(cp_id_instr_category) intersect {InstrCategoryNone} &&
        binsof(cp_id_stage_state) intersect {PipeStageEmpty};
    }

    interrupt_taken_instr_cross: cross cp_interrupt_taken, instr_unstalled_last,
      cp_id_instr_category_last;

    debug_instruction_cross: cross cp_debug_mode, cp_id_instr_category;

    debug_entry_if_instr_cross: cross cp_debug_entry_if, instr_unstalled_last,
      cp_id_instr_category_last;
    pipe_flush_instr_cross: cross cp_pipe_flush, instr_unstalled, cp_id_instr_category;

    exception_stall_instr_cross: cross cp_ls_pmp_exception, cp_ls_error_exception,
      cp_id_instr_category, cp_stall_type_id, instr_unstalled, cp_irq_pending, cp_debug_req {
      illegal_bins illegal =
        // Only Div, Mul, Branch and Jump instructions can see an instruction stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryDiv, InstrCategoryMul,
                                                 InstrCategoryBranch, InstrCategoryJump} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeInstr})
    ||
        // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSR Access can see a load hazard stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryALU, InstrCategoryMul,
                                                 InstrCategoryDiv, InstrCategoryBranch,
                                                 InstrCategoryJump, InstrCategoryLoad,
                                                 InstrCategoryStore, InstrCategoryCSRAccess} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeLdHz});

      // Cannot have a memory stall when we see an LS exception unless it is a load or store
      // instruction
      illegal_bins mem_stall_illegal =
        (!binsof(cp_id_instr_category) intersect {InstrCategoryLoad, InstrCategoryStore} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeMem}) with
        (cp_ls_pmp_exception == 1'b1 || cp_ls_error_exception == 1'b1);

      // When pipeline has unstalled stall type will always be none
      illegal_bins unstalled_illegal =
        !binsof(cp_stall_type_id) intersect {IdStallTypeNone} with (instr_unstalled == 1'b1);
    }

    csr_read_only_priv_cross: cross cp_csr_read_only, cp_priv_mode_id;
    csr_write_priv_cross: cross cp_csr_write, cp_priv_mode_id;

    csr_read_only_debug_cross: cross cp_csr_read_only, cp_debug_mode {
      // Only care about specific debug CSRs
      ignore_bins ignore = !binsof(cp_csr_read_only) intersect {`DEBUG_CSRS};
    }

    csr_write_debug_cross: cross cp_csr_write, cp_debug_mode {
      // Only care about specific debug CSRs
      ignore_bins ignore = !binsof(cp_csr_write) intersect {`DEBUG_CSRS};
    }
  endgroup

  bit en_uarch_cov;

  initial begin
   void'($value$plusargs("enable_ibex_fcov=%d", en_uarch_cov));
  end

  `DV_FCOV_INSTANTIATE_CG(uarch_cg, en_uarch_cov)
endinterface
