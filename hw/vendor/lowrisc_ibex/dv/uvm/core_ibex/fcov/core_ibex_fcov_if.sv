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
  input fcov_csr_write,

  input fcov_rf_ecc_err_a_id,
  input fcov_rf_ecc_err_b_id,

  input ibex_mubi_t fetch_enable_i,

  input instr_req_o,
  input instr_gnt_i,
  input instr_rvalid_i,

  input data_req_o,
  input data_gnt_i,
  input data_rvalid_i
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
      ~id_stage_i.div_sel_ex_o && ~id_stage_i.lsu_req_dec && ~id_stage_i.jump_in_dec)

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

  // This latch is needed because if we cannot register this condition being true
  // with a clock. Being in the sleep mode implies that we don't have an active clock.
  // So, we need to catch the condition, latch it and keep it until we wake up and decode
  // an instruction (which guarantees we have a clock in the core)
  logic kept_wfi_with_irq;

  always_latch begin
    if (id_stage_i.controller_i.ctrl_fsm_cs == DECODE) begin
      kept_wfi_with_irq = 1'b0;
    end else if (id_stage_i.controller_i.ctrl_fsm_cs == SLEEP &&
                 id_stage_i.controller_i.ctrl_fsm_ns == SLEEP &&
                 (|cs_registers_i.mip)) begin
      kept_wfi_with_irq = 1'b1;
    end
  end

  logic instr_id_matches_trigger_d, instr_id_matches_trigger_q;

  assign instr_id_matches_trigger_d = id_stage_i.controller_i.trigger_match_i &&
                                      id_stage_i.controller_i.fcov_debug_entry_if;

  // Delay instruction matching trigger point since it is cached in IF stage.
  // We would want to cross it with decoded instruction categories and it does not matter
  // when exactly we are hitting the condition.
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      instr_id_matches_trigger_q <= 1'b0;
    end else begin
      instr_id_matches_trigger_q <= instr_id_matches_trigger_d;
    end
  end

  // Keep track of previous data addr of Store to catch RAW hazard caused by STORE->LOAD
  logic [31:0]     prev_store_addr;
  logic [31:0]     data_addr_incr;
  logic [31:0]     curr_data_addr;
  logic            raw_hz;

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_store_addr <= 1'b0;
    end else if (load_store_unit_i.data_we_o) begin
      // It does not matter if the store we executed before load is misaligned or not. Because
      // even if it is misaligned, we would catch the "corrected" version (2nd access) before
      // doing the RAW hazard check.
      prev_store_addr <= load_store_unit_i.data_addr_o;
    end
  end

  // Calculate the corrected version of the new data addr at the same time while LOAD instruction
  // gets decoded.
  always_comb begin
    if (load_store_unit_i.split_misaligned_access) begin
      data_addr_incr = load_store_unit_i.data_addr + 4;
      curr_data_addr = {data_addr_incr[2+:30],2'b00};
    end else begin
      curr_data_addr = load_store_unit_i.data_addr;
    end
  end

  // If we have LOAD at ID/EX stage and STORE at WB stage, compare the calculated address for LOAD
  // and the saved STORE address. If they are matching we would have RAW hazard.
  assign raw_hz = wb_stage_i.outstanding_store_wb_o &&
                  id_instr_category == InstrCategoryLoad &&
                  prev_store_addr == curr_data_addr;

  // Collect all the interrupts for collecting them in different bins.
  logic [5:0] fcov_irqs;

  assign fcov_irqs = {id_stage_i.controller_i.irq_nm_ext_i,
                      id_stage_i.controller_i.irq_nm_int,
                      (|id_stage_i.controller_i.irqs_i.irq_fast),
                      id_stage_i.controller_i.irqs_i.irq_external,
                      id_stage_i.controller_i.irqs_i.irq_software,
                      id_stage_i.controller_i.irqs_i.irq_timer};

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

  // V2S Related Probes for Top-Level
  logic rf_glitch_err;
  logic lockstep_glitch_err;

  logic imem_single_cycle_response, dmem_single_cycle_response;

  mem_monitor_if iside_mem_monitor(
    .clk_i,
    .rst_ni,
    .req_i(instr_req_o),
    .gnt_i(instr_gnt_i),
    .rvalid_i(instr_rvalid_i),
    .outstanding_requests_o(),
    .single_cycle_response_o(imem_single_cycle_response)
  );

  mem_monitor_if dside_mem_monitor(
    .clk_i,
    .rst_ni,
    .req_i(data_req_o),
    .gnt_i(data_gnt_i),
    .rvalid_i(data_rvalid_i),
    .outstanding_requests_o(),
    .single_cycle_response_o(dmem_single_cycle_response)
  );

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

    cp_mem_raw_hz: coverpoint raw_hz;

    cp_mprv: coverpoint cs_registers_i.mstatus_q.mprv;

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

    // V2S Coverpoints
    cp_data_ind_timing: coverpoint cs_registers_i.data_ind_timing_o;
    cp_data_ind_timing_instr: coverpoint id_instr_category iff (cs_registers_i.data_ind_timing_o) {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    cp_dummy_instr_en: coverpoint cs_registers_i.dummy_instr_en_o;
    cp_dummy_instr_mask: coverpoint cs_registers_i.dummy_instr_mask_o;
    cp_dummy_instr_type: coverpoint if_stage_i.fcov_dummy_instr_type;
    cp_dummy_instr: coverpoint id_instr_category iff (cs_registers_i.dummy_instr_en_o) {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal = {InstrCategoryOther, InstrCategoryOtherIllegal};
    }

    // Each stage sees a dummy instruction.
    cp_dummy_instr_if_stage: coverpoint if_stage_i.fcov_insert_dummy_instr;
    cp_dummy_instr_id_stage: coverpoint if_stage_i.dummy_instr_id_o;
    cp_dummy_instr_wb_stage: coverpoint wb_stage_i.dummy_instr_wb_o;

    `DV_FCOV_EXPR_SEEN(rf_a_ecc_err, fcov_rf_ecc_err_a_id)
    `DV_FCOV_EXPR_SEEN(rf_b_ecc_err, fcov_rf_ecc_err_b_id)

    `DV_FCOV_EXPR_SEEN(icache_ecc_err, if_stage_i.icache_ecc_error_o)

    `DV_FCOV_EXPR_SEEN(mem_load_ecc_err, load_store_unit_i.load_resp_intg_err_o)
    `DV_FCOV_EXPR_SEEN(mem_store_ecc_err, load_store_unit_i.store_resp_intg_err_o)

    `DV_FCOV_EXPR_SEEN(lockstep_err, lockstep_glitch_err)
    `DV_FCOV_EXPR_SEEN(rf_glitch_err, rf_glitch_err)
    `DV_FCOV_EXPR_SEEN(pc_mismatch_err, if_stage_i.pc_mismatch_alert_o)

    cp_fetch_enable: coverpoint fetch_enable_i {
      bins fetch_on    = {IbexMuBiOn};
      bins fetch_off   = {IbexMuBiOff};
      bins fetch_inval = default;
    }

    // TODO: MRET/WFI in debug mode?
    // Specific cover points for these as `id_instr_category` will be InstrCategoryPrivIllegal when
    // executing these instructions in U-mode.
    `DV_FCOV_EXPR_SEEN(mret_in_umode, id_stage_i.mret_insn_dec && priv_mode_id == PRIV_LVL_U)
    `DV_FCOV_EXPR_SEEN(wfi_in_umode, id_stage_i.wfi_insn_dec && priv_mode_id == PRIV_LVL_U)

    // Unsupported writes to WARL type CSRs
    `DV_FCOV_EXPR_SEEN(warl_check_mstatus,
                       fcov_csr_write &&
                       (cs_registers_i.u_mstatus_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mie,
                       fcov_csr_write &&
                       (cs_registers_i.u_mie_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mtvec,
                       fcov_csr_write &&
                       (cs_registers_i.u_mtvec_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mepc,
                       fcov_csr_write &&
                       (cs_registers_i.u_mepc_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_mtval,
                       fcov_csr_write &&
                       (cs_registers_i.u_mtval_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_dcsr,
                       fcov_csr_write &&
                       (cs_registers_i.u_dcsr_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(warl_check_cpuctrl,
                       fcov_csr_write &&
                       (cs_registers_i.u_cpuctrlsts_part_csr.wr_data_i !=
                       cs_registers_i.csr_wdata_int))

    `DV_FCOV_EXPR_SEEN(double_fault, cs_registers_i.cpuctrlsts_part_d.double_fault_seen)
    `DV_FCOV_EXPR_SEEN(icache_enable, cs_registers_i.cpuctrlsts_part_d.icache_enable)

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

    `DV_FCOV_EXPR_SEEN(debug_wakeup, id_stage_i.controller_i.fcov_debug_wakeup)
    `DV_FCOV_EXPR_SEEN(all_debug_req, id_stage_i.controller_i.fcov_all_debug_req)
    `DV_FCOV_EXPR_SEEN(debug_entry_if, id_stage_i.controller_i.fcov_debug_entry_if)
    `DV_FCOV_EXPR_SEEN(debug_entry_id, id_stage_i.controller_i.fcov_debug_entry_id)
    `DV_FCOV_EXPR_SEEN(pipe_flush, id_stage_i.controller_i.fcov_pipe_flush)
    `DV_FCOV_EXPR_SEEN(single_step_taken, id_stage_i.controller_i.fcov_debug_single_step_taken)
    `DV_FCOV_EXPR_SEEN(single_step_exception, id_stage_i.controller_i.do_single_step_d &&
                                              id_stage_i.controller_i.fcov_pipe_flush)
    `DV_FCOV_EXPR_SEEN(insn_trigger_enter_debug, instr_id_matches_trigger_q)

    cp_nmi_taken: coverpoint ((fcov_irqs[5] || fcov_irqs[4])) iff
                             (id_stage_i.controller_i.fcov_interrupt_taken);

    cp_interrupt_taken: coverpoint fcov_irqs iff (id_stage_i.controller_i.fcov_interrupt_taken){
      wildcard bins nmi_external  = {6'b1?????};
      wildcard bins nmi_internal  = {6'b01????};
      wildcard bins irq_fast      = {6'b001???};
      wildcard bins irq_external  = {6'b0001??};
      wildcard bins irq_software  = {6'b00001?};
      wildcard bins irq_timer     = {6'b000001};
    }

    cp_controller_fsm: coverpoint id_stage_i.controller_i.ctrl_fsm_cs {
      bins out_of_reset = (RESET => BOOT_SET);
      bins out_of_boot_set = (BOOT_SET => FIRST_FETCH);
      bins out_of_first_fetch0 = (FIRST_FETCH => DECODE);
      bins out_of_first_fetch1 = (FIRST_FETCH => IRQ_TAKEN);
      bins out_of_first_fetch2 = (FIRST_FETCH => DBG_TAKEN_IF);
      bins out_of_decode0 = (DECODE => FLUSH);
      bins out_of_decode1 = (DECODE => DBG_TAKEN_IF);
      bins out_of_decode2 = (DECODE => IRQ_TAKEN);
      bins out_of_irq_taken = (IRQ_TAKEN => DECODE);
      bins out_of_debug_taken_if = (DBG_TAKEN_IF => DECODE);
      bins out_of_debug_taken_id = (DBG_TAKEN_ID => DECODE);
      bins out_of_flush0 = (FLUSH => DECODE);
      bins out_of_flush1 = (FLUSH => DBG_TAKEN_ID);
      bins out_of_flush2 = (FLUSH => WAIT_SLEEP);
      bins out_of_flush3 = (FLUSH => DBG_TAKEN_IF);
      bins out_of_wait_sleep = (WAIT_SLEEP => SLEEP);
      bins out_of_sleep = (SLEEP => FIRST_FETCH);
      // TODO: VCS does not implement default sequence so illegal_bins will be empty
      illegal_bins illegal_transitions = default sequence;
    }

    cp_controller_fsm_sleep: coverpoint id_stage_i.controller_i.ctrl_fsm_cs {
      bins out_of_sleep = (SLEEP => FIRST_FETCH);
      bins enter_sleep = (WAIT_SLEEP => SLEEP);
      // TODO: VCS does not implement default sequence so illegal_bins will be empty
      illegal_bins illegal_transitions = default sequence;
    }

    // This will only be seen when specific interrupt is disabled by MIE CSR
    `DV_FCOV_EXPR_SEEN(irq_continue_sleep, kept_wfi_with_irq)

    cp_single_step_instr: coverpoint id_instr_category iff
                                     (id_stage_i.controller_i.fcov_debug_single_step_taken) {
      // Not certain if InstrCategoryOtherIllegal can occur. Put it in illegal_bins for now and
      // revisit if any issues are seen
      illegal_bins illegal =
        {InstrCategoryOther, InstrCategoryNone, InstrCategoryOtherIllegal
         // [Debug Spec v1.0.0-STABLE, p.95]
         // > dret is an instruction which only has meaning while Debug Mode
         // We want to step over this to at-least specify how the Ibex does behave.
         //
         // [Debug Spec v1.0.0-STABLE, p.50]
         // > If the instruction being stepped over is wfi and would normally stall the hart,
         // > then instead the instruction is treated as nop.
         // Again this will be useful coverage to verify we are testing this behaviour.
        };
    }

    // Only sample the bus error from the first access of misaligned load/store when we are in
    // the data phase of the second access. Without this, we cannot sample the case when both
    // first and second access fails.
    cp_misaligned_first_data_bus_err: coverpoint load_store_unit_i.fcov_mis_bus_err_1_q iff
      (load_store_unit_i.fcov_mis_rvalid_2);

    cp_misaligned_second_data_bus_err: coverpoint load_store_unit_i.data_bus_err_i iff
      (load_store_unit_i.fcov_mis_rvalid_2);

    cp_imem_response_latency: coverpoint imem_single_cycle_response iff (instr_rvalid_i) {
      bins single_cycle = {1'b1};
      bins multi_cycle = {1'b0};
    }

    `DV_FCOV_EXPR_SEEN(imem_req_gnt_rvalid, instr_rvalid_i & instr_req_o & instr_gnt_i)

    cp_dmem_response_latency: coverpoint dmem_single_cycle_response iff (data_rvalid_i) {
      bins single_cycle = {1'b1};
      bins multi_cycle = {1'b0};
    }

    `DV_FCOV_EXPR_SEEN(dmem_req_gnt_rvalid, data_rvalid_i & data_req_o & data_gnt_i)

    misaligned_data_bus_err_cross: cross cp_misaligned_first_data_bus_err,
                                         cp_misaligned_second_data_bus_err {
      // Cannot see both bus errors together as they're signalled at different states of the load
      // store unit FSM
      illegal_bins illegal = binsof(cp_misaligned_first_data_bus_err) intersect {1'b1} &&
        binsof(cp_misaligned_second_data_bus_err) intersect {1'b1};
    }

    misaligned_insn_bus_err_cross: cross id_stage_i.instr_fetch_err_i,
                                         id_stage_i.instr_fetch_err_plus2_i;

    // Include both mstatus.mie enabled/disabled because it should not affect wakeup condition
    irq_wfi_cross: cross cp_controller_fsm_sleep, cs_registers_i.mstatus_q.mie iff
                         (id_stage_i.irq_pending_i | id_stage_i.irq_nm_i);

    debug_wfi_cross: cross cp_controller_fsm_sleep, cp_all_debug_req iff
                           (id_stage_i.controller_i.fcov_all_debug_req);

    priv_mode_instr_cross: cross cp_priv_mode_id, cp_id_instr_category {
      // No un-privileged CSRs on Ibex so no InstrCategoryCSRAccess in U mode (any CSR instruction
      // becomes InstrCategoryCSRIllegal).
      illegal_bins umode_csr_access_illegal =
        binsof(cp_id_instr_category) intersect {InstrCategoryCSRAccess} &&
        binsof(cp_priv_mode_id) intersect {PRIV_LVL_U};
    }

    priv_mode_irq_cross: cross cp_priv_mode_id, cp_interrupt_taken, cs_registers_i.mstatus_q.mie {
      // No interrupt would be taken in M-mode when its mstatus.MIE = 0 unless it's an NMI
      illegal_bins mmode_mstatus_mie =
        binsof(cs_registers_i.mstatus_q.mie) intersect {1'b0} &&
        binsof(cp_priv_mode_id) intersect {PRIV_LVL_M} with (cp_interrupt_taken >> 4 == 6'd0);
    }

    priv_mode_exception_cross: cross cp_priv_mode_id, cp_ls_pmp_exception, cp_ls_error_exception {
      illegal_bins pmp_and_error_exeption_both =
        (binsof(cp_ls_pmp_exception) intersect {1'b1} &&
         binsof(cp_ls_error_exception) intersect {1'b1});
    }

    stall_cross: cross cp_id_instr_category, cp_stall_type_id {
      illegal_bins illegal =
        // Only Div, Mul, Branch and Jump instructions can see an instruction stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryDiv, InstrCategoryMul,
                                                 InstrCategoryBranch, InstrCategoryJump,
                                                 InstrCategoryFenceI} &&
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
      // When ID stage is empty the only legal instruction category is InstrCategoryNone. Conversly
      // when the instruction category is InstrCategoryNone the only legal ID stage state is
      // PipeStageEmpty.
      illegal_bins illegal = (!binsof(cp_id_instr_category) intersect {InstrCategoryNone} &&
        binsof(cp_id_stage_state) intersect {PipeStageEmpty}) ||
      (binsof(cp_id_instr_category) intersect {InstrCategoryNone} &&
        !binsof(cp_id_stage_state) intersect {PipeStageEmpty});
    }

    interrupt_taken_instr_cross: cross cp_nmi_taken, instr_unstalled_last,
      cp_id_instr_category_last iff (id_stage_i.controller_i.fcov_interrupt_taken);

    debug_instruction_cross: cross cp_debug_mode, cp_id_instr_category;

    debug_entry_if_instr_cross: cross cp_debug_entry_if, instr_unstalled_last,
      cp_id_instr_category_last;
    pipe_flush_instr_cross: cross cp_pipe_flush, instr_unstalled, cp_id_instr_category;

    exception_stall_instr_cross: cross cp_ls_pmp_exception, cp_ls_error_exception,
      cp_id_instr_category, cp_stall_type_id, instr_unstalled, cp_irq_pending, cp_debug_req {
      illegal_bins illegal =
        // Only Div, Mul, Branch and Jump instructions can see an instruction stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryDiv, InstrCategoryMul,
                                                 InstrCategoryBranch, InstrCategoryJump,
                                                 InstrCategoryFenceI} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeInstr})
    ||
        // Only ALU, Mul, Div, Branch, Jump, Load, Store and CSR Access can see a load hazard stall
        (!binsof(cp_id_instr_category) intersect {InstrCategoryALU, InstrCategoryMul,
                                                 InstrCategoryDiv, InstrCategoryBranch,
                                                 InstrCategoryJump, InstrCategoryLoad,
                                                 InstrCategoryStore, InstrCategoryCSRAccess} &&
         binsof(cp_stall_type_id) intersect {IdStallTypeLdHz});

      // Cannot have a memory stall when we see an LS exception unless it is a load or store
      // instruction or a fetch error (the raw instruction decode can still indicate a load or store
      // which produces a stall, though won't cause any load or store to occur due to the fetch
      // error).
      illegal_bins mem_stall_illegal =
        (!binsof(cp_id_instr_category) intersect {InstrCategoryLoad, InstrCategoryStore,
                                                  InstrCategoryFetchError} &&
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

    // V2S Crosses

    dummy_instr_config_cross: cross cp_dummy_instr_type, cp_dummy_instr_mask
                                iff (cs_registers_i.dummy_instr_en_o);

    rf_ecc_err_cross: cross fcov_rf_ecc_err_a_id, fcov_rf_ecc_err_b_id
                                iff (id_stage_i.instr_valid_i);

    // Each stage sees a debug request while executing a dummy instruction.
    debug_req_dummy_instr_if_stage_cross: cross cp_debug_req, cp_dummy_instr_if_stage;
    debug_req_dummy_instr_id_stage_cross: cross cp_debug_req, cp_dummy_instr_id_stage;
    debug_req_dummy_instr_wb_stage_cross: cross cp_debug_req, cp_dummy_instr_wb_stage;

    // Each stage sees an interrupt request while executing a dummy instruction.
    irq_pending_dummy_instr_if_stage_cross: cross cp_irq_pending, cp_dummy_instr_if_stage;
    irq_pending_dummy_instr_id_stage_cross: cross cp_irq_pending, cp_dummy_instr_id_stage;
    irq_pending_dummy_instr_wb_stage_cross: cross cp_irq_pending, cp_dummy_instr_wb_stage;

  endgroup

  bit en_uarch_cov;

  initial begin
   void'($value$plusargs("enable_ibex_fcov=%d", en_uarch_cov));
  end

  `DV_FCOV_INSTANTIATE_CG(uarch_cg, en_uarch_cov)
endinterface

interface mem_monitor_if (
  input clk_i,
  input rst_ni,

  input req_i,
  input gnt_i,
  input rvalid_i,

  output int   outstanding_requests_o,
  output logic single_cycle_response_o
);

  int outstanding_requests;
  logic outstanding_requests_inc, outstanding_requests_dec;
  logic no_outstanding_requests_last_cycle;

  assign outstanding_requests_inc = req_i & gnt_i;
  assign outstanding_requests_dec = rvalid_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      outstanding_requests               <= 0;
      no_outstanding_requests_last_cycle <= 1'b0;
    end else begin
      if (outstanding_requests_inc && !outstanding_requests_dec) begin
        outstanding_requests <= outstanding_requests + 1;
      end else if (!outstanding_requests_inc && outstanding_requests_dec) begin
        outstanding_requests <= outstanding_requests - 1;
      end

      no_outstanding_requests_last_cycle <= (outstanding_requests == 0) ||
        ((outstanding_requests == 1) && outstanding_requests_dec);
    end
  end

  assign outstanding_requests_o = outstanding_requests;
  assign single_cycle_response_o = no_outstanding_requests_last_cycle & rvalid_i;
endinterface
