// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Main controller of the processor
 */

`include "prim_assert.sv"

module ibex_controller #(
    parameter bit WritebackStage  = 0,
    parameter bit BranchPredictor = 0
 ) (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    output logic                  ctrl_busy_o,           // core is busy processing instrs

    // decoder related signals
    input  logic                  illegal_insn_i,          // decoder has an invalid instr
    input  logic                  ecall_insn_i,            // decoder has ECALL instr
    input  logic                  mret_insn_i,             // decoder has MRET instr
    input  logic                  dret_insn_i,             // decoder has DRET instr
    input  logic                  wfi_insn_i,              // decoder has WFI instr
    input  logic                  ebrk_insn_i,             // decoder has EBREAK instr
    input  logic                  csr_pipe_flush_i,        // do CSR-related pipeline flush

    // instr from IF-ID pipeline stage
    input  logic                  instr_valid_i,           // instr is valid
    input  logic [31:0]           instr_i,                 // uncompressed instr data for mtval
    input  logic [15:0]           instr_compressed_i,      // instr compressed data for mtval
    input  logic                  instr_is_compressed_i,   // instr is compressed
    input  logic                  instr_bp_taken_i,        // instr was predicted taken branch
    input  logic                  instr_fetch_err_i,       // instr has error
    input  logic                  instr_fetch_err_plus2_i, // instr error is x32
    input  logic [31:0]           pc_id_i,                 // instr address

    // to IF-ID pipeline stage
    output logic                  instr_valid_clear_o,     // kill instr in IF-ID reg
    output logic                  id_in_ready_o,           // ID stage is ready for new instr
    output logic                  controller_run_o,        // Controller is in standard instruction
                                                           // run mode

    // to prefetcher
    output logic                  instr_req_o,             // start fetching instructions
    output logic                  pc_set_o,                // jump to address set by pc_mux
    output logic                  pc_set_spec_o,           // speculative branch
    output ibex_pkg::pc_sel_e     pc_mux_o,                // IF stage fetch address selector
                                                           // (boot, normal, exception...)
    output logic                  nt_branch_mispredict_o,  // Not-taken branch in ID/EX was
                                                           // mispredicted (predicted taken)
    output ibex_pkg::exc_pc_sel_e exc_pc_mux_o,            // IF stage selector for exception PC
    output ibex_pkg::exc_cause_e  exc_cause_o,             // for IF stage, CSRs

    // LSU
    input  logic [31:0]           lsu_addr_last_i,         // for mtval
    input  logic                  load_err_i,
    input  logic                  store_err_i,
    output logic                  wb_exception_o,          // Instruction in WB taking an exception

    // jump/branch signals
    input  logic                  branch_set_i,            // branch set signal (branch definitely
                                                           // taken)
    input  logic                  branch_set_spec_i,       // speculative branch signal (branch
                                                           // may be taken)
    input  logic                  branch_not_set_i,        // branch is definitely not taken
    input  logic                  jump_set_i,              // jump taken set signal

    // interrupt signals
    input  logic                  csr_mstatus_mie_i,       // M-mode interrupt enable bit
    input  logic                  irq_pending_i,           // interrupt request pending
    input  ibex_pkg::irqs_t       irqs_i,                  // interrupt requests qualified with
                                                           // mie CSR
    input  logic                  irq_nm_i,                // non-maskeable interrupt
    output logic                  nmi_mode_o,              // core executing NMI handler

    // debug signals
    input  logic                  debug_req_i,
    output ibex_pkg::dbg_cause_e  debug_cause_o,
    output logic                  debug_csr_save_o,
    output logic                  debug_mode_o,
    input  logic                  debug_single_step_i,
    input  logic                  debug_ebreakm_i,
    input  logic                  debug_ebreaku_i,
    input  logic                  trigger_match_i,

    output logic                  csr_save_if_o,
    output logic                  csr_save_id_o,
    output logic                  csr_save_wb_o,
    output logic                  csr_restore_mret_id_o,
    output logic                  csr_restore_dret_id_o,
    output logic                  csr_save_cause_o,
    output logic [31:0]           csr_mtval_o,
    input  ibex_pkg::priv_lvl_e   priv_mode_i,
    input  logic                  csr_mstatus_tw_i,

    // stall & flush signals
    input  logic                  stall_id_i,
    input  logic                  stall_wb_i,
    output logic                  flush_id_o,
    input  logic                  ready_wb_i,

    // performance monitors
    output logic                  perf_jump_o,             // we are executing a jump
                                                           // instruction (j, jr, jal, jalr)
    output logic                  perf_tbranch_o           // we are executing a taken branch
                                                           // instruction
);
  import ibex_pkg::*;

  // FSM state encoding
  typedef enum logic [3:0] {
    RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH, DECODE, FLUSH,
    IRQ_TAKEN, DBG_TAKEN_IF, DBG_TAKEN_ID
  } ctrl_fsm_e;

  ctrl_fsm_e ctrl_fsm_cs, ctrl_fsm_ns;

  logic nmi_mode_q, nmi_mode_d;
  logic debug_mode_q, debug_mode_d;
  logic load_err_q, load_err_d;
  logic store_err_q, store_err_d;
  logic exc_req_q, exc_req_d;
  logic illegal_insn_q, illegal_insn_d;

  // Of the various exception/fault signals, which one takes priority in FLUSH and hence controls
  // what happens next (setting exc_cause, csr_mtval etc)
  logic instr_fetch_err_prio;
  logic illegal_insn_prio;
  logic ecall_insn_prio;
  logic ebrk_insn_prio;
  logic store_err_prio;
  logic load_err_prio;

  logic stall;
  logic halt_if;
  logic retain_id;
  logic flush_id;
  logic illegal_dret;
  logic illegal_umode;
  logic exc_req_lsu;
  logic special_req_all;
  logic special_req_branch;
  logic enter_debug_mode;
  logic ebreak_into_debug;
  logic handle_irq;

  logic [3:0] mfip_id;
  logic       unused_irq_timer;

  logic ecall_insn;
  logic mret_insn;
  logic dret_insn;
  logic wfi_insn;
  logic ebrk_insn;
  logic csr_pipe_flush;
  logic instr_fetch_err;

`ifndef SYNTHESIS
  // synopsys translate_off
  // make sure we are called later so that we do not generate messages for
  // glitches
  always_ff @(negedge clk_i) begin
    // print warning in case of decoding errors
    if ((ctrl_fsm_cs == DECODE) && instr_valid_i && !instr_fetch_err_i && illegal_insn_d) begin
      $display("%t: Illegal instruction (hart %0x) at PC 0x%h: 0x%h", $time, ibex_core.hart_id_i,
               ibex_id_stage.pc_id_i, ibex_id_stage.instr_rdata_i);
    end
  end
  // synopsys translate_on
`endif

  ////////////////
  // Exceptions //
  ////////////////

  assign load_err_d  = load_err_i;
  assign store_err_d = store_err_i;

  // Decoder doesn't take instr_valid into account, factor it in here.
  assign ecall_insn      = ecall_insn_i      & instr_valid_i;
  assign mret_insn       = mret_insn_i       & instr_valid_i;
  assign dret_insn       = dret_insn_i       & instr_valid_i;
  assign wfi_insn        = wfi_insn_i        & instr_valid_i;
  assign ebrk_insn       = ebrk_insn_i       & instr_valid_i;
  assign csr_pipe_flush  = csr_pipe_flush_i  & instr_valid_i;
  assign instr_fetch_err = instr_fetch_err_i & instr_valid_i;

  // "Executing DRET outside of Debug Mode causes an illegal instruction exception."
  // [Debug Spec v0.13.2, p.41]
  assign illegal_dret = dret_insn & ~debug_mode_q;

  // Some instructions can only be executed in M-Mode
  assign illegal_umode = (priv_mode_i != PRIV_LVL_M) &
                         // MRET must be in M-Mode. TW means trap WFI to M-Mode.
                         (mret_insn | (csr_mstatus_tw_i & wfi_insn));

  // This is recorded in the illegal_insn_q flop to help timing.  Specifically
  // it is needed to break the path from ibex_cs_registers/illegal_csr_insn_o
  // to pc_set_o.  Clear when controller is in FLUSH so it won't remain set
  // once illegal instruction is handled.
  // All terms in this expression are qualified by instr_valid_i
  assign illegal_insn_d = (illegal_insn_i | illegal_dret | illegal_umode) & (ctrl_fsm_cs != FLUSH);

  // exception requests
  // requests are flopped in exc_req_q.  This is cleared when controller is in
  // the FLUSH state so the cycle following exc_req_q won't remain set for an
  // exception request that has just been handled.
  // All terms in this expression are qualified by instr_valid_i
  assign exc_req_d = (ecall_insn | ebrk_insn | illegal_insn_d | instr_fetch_err) &
                     (ctrl_fsm_cs != FLUSH);

  // LSU exception requests
  assign exc_req_lsu = store_err_i | load_err_i;


  // special requests: special instructions, pipeline flushes, exceptions...

  // To avoid creating a path from data_err_i -> instr_req_o and to help timing the below
  // special_req_all has a version that only applies to branches. For a branch the controller needs
  // to set pc_set_o but only if there is no special request. If the generic special_req_all signal
  // is used then a variety of signals that will never cause a special request during a branch
  // instruction end up factored into pc_set_o. The special_req_branch only considers the special
  // request reasons that are relevant to a branch.

  // generic special request signal, applies to all instructions
  // All terms in this expression are qualified by instr_valid_i except exc_req_lsu which can come
  // from the Writeback stage with no instr_valid_i from the ID stage
  assign special_req_all = mret_insn | dret_insn | wfi_insn | csr_pipe_flush |
      exc_req_d | exc_req_lsu;

  // special request that can specifically occur during branch instructions
  // All terms in this expression are qualified by instr_valid_i
  assign special_req_branch = instr_fetch_err & (ctrl_fsm_cs != FLUSH);

  `ASSERT(SpecialReqBranchGivesSpecialReqAll,
    special_req_branch |-> special_req_all)

  `ASSERT(SpecialReqAllGivesSpecialReqBranchIfBranchInst,
    special_req_all && (branch_set_i || jump_set_i) |-> special_req_branch)

  // Exception/fault prioritisation is taken from Table 3.7 of Priviledged Spec v1.11
  if (WritebackStage) begin : g_wb_exceptions
    always_comb begin
      instr_fetch_err_prio = 0;
      illegal_insn_prio    = 0;
      ecall_insn_prio      = 0;
      ebrk_insn_prio       = 0;
      store_err_prio       = 0;
      load_err_prio        = 0;

      // Note that with the writeback stage store/load errors occur on the instruction in writeback,
      // all other exception/faults occur on the instruction in ID/EX. The faults from writeback
      // must take priority as that instruction is architecurally ordered before the one in ID/EX.
      if (store_err_q) begin
        store_err_prio = 1'b1;
      end else if (load_err_q) begin
        load_err_prio  = 1'b1;
      end else if (instr_fetch_err) begin
        instr_fetch_err_prio = 1'b1;
      end else if (illegal_insn_q) begin
        illegal_insn_prio = 1'b1;
      end else if (ecall_insn) begin
        ecall_insn_prio = 1'b1;
      end else if (ebrk_insn) begin
        ebrk_insn_prio = 1'b1;
      end
    end

    // Instruction in writeback is generating an exception so instruction in ID must not execute
    assign wb_exception_o = load_err_q | store_err_q | load_err_i | store_err_i;
  end else begin : g_no_wb_exceptions
    always_comb begin
      instr_fetch_err_prio = 0;
      illegal_insn_prio    = 0;
      ecall_insn_prio      = 0;
      ebrk_insn_prio       = 0;
      store_err_prio       = 0;
      load_err_prio        = 0;

      if (instr_fetch_err) begin
        instr_fetch_err_prio = 1'b1;
      end else if (illegal_insn_q) begin
        illegal_insn_prio = 1'b1;
      end else if (ecall_insn) begin
        ecall_insn_prio = 1'b1;
      end else if (ebrk_insn) begin
        ebrk_insn_prio = 1'b1;
      end else if (store_err_q) begin
        store_err_prio = 1'b1;
      end else if (load_err_q) begin
        load_err_prio  = 1'b1;
      end
    end
    assign wb_exception_o = 1'b0;
  end

  `ASSERT_IF(IbexExceptionPrioOnehot,
             $onehot({instr_fetch_err_prio,
                      illegal_insn_prio,
                      ecall_insn_prio,
                      ebrk_insn_prio,
                      store_err_prio,
                      load_err_prio}),
             (ctrl_fsm_cs == FLUSH) & exc_req_q)

  ////////////////
  // Interrupts //
  ////////////////

  // Enter debug mode due to an external debug_req_i or because the core is in
  // single step mode (dcsr.step == 1). Single step must be qualified with
  // instruction valid otherwise the core will immediately enter debug mode
  // due to a recently flushed IF (or a delay in an instruction returning from
  // memory) before it has had anything to single step.
  // Also enter debug mode on a trigger match (hardware breakpoint)
  assign enter_debug_mode = (debug_req_i | (debug_single_step_i & instr_valid_i) |
                             trigger_match_i) & ~debug_mode_q;

  // Set when an ebreak should enter debug mode rather than jump to exception
  // handler
  assign ebreak_into_debug = priv_mode_i == PRIV_LVL_M ? debug_ebreakm_i :
                             priv_mode_i == PRIV_LVL_U ? debug_ebreaku_i :
                                                         1'b0;

  // Interrupts including NMI are ignored,
  // - while in debug mode [Debug Spec v0.13.2, p.39],
  // - while in NMI mode (nested NMIs are not supported, NMI has highest priority and
  //   cannot be interrupted by regular interrupts).
  assign handle_irq = ~debug_mode_q & ~nmi_mode_q &
      (irq_nm_i | (irq_pending_i & csr_mstatus_mie_i));

  // generate ID of fast interrupts, highest priority to highest ID
  always_comb begin : gen_mfip_id
    if      (irqs_i.irq_fast[14]) mfip_id = 4'd14;
    else if (irqs_i.irq_fast[13]) mfip_id = 4'd13;
    else if (irqs_i.irq_fast[12]) mfip_id = 4'd12;
    else if (irqs_i.irq_fast[11]) mfip_id = 4'd11;
    else if (irqs_i.irq_fast[10]) mfip_id = 4'd10;
    else if (irqs_i.irq_fast[ 9]) mfip_id = 4'd9;
    else if (irqs_i.irq_fast[ 8]) mfip_id = 4'd8;
    else if (irqs_i.irq_fast[ 7]) mfip_id = 4'd7;
    else if (irqs_i.irq_fast[ 6]) mfip_id = 4'd6;
    else if (irqs_i.irq_fast[ 5]) mfip_id = 4'd5;
    else if (irqs_i.irq_fast[ 4]) mfip_id = 4'd4;
    else if (irqs_i.irq_fast[ 3]) mfip_id = 4'd3;
    else if (irqs_i.irq_fast[ 2]) mfip_id = 4'd2;
    else if (irqs_i.irq_fast[ 1]) mfip_id = 4'd1;
    else                          mfip_id = 4'd0;
  end

  assign unused_irq_timer = irqs_i.irq_timer;

  /////////////////////
  // Core controller //
  /////////////////////

  always_comb begin
    // Default values
    instr_req_o           = 1'b1;

    csr_save_if_o         = 1'b0;
    csr_save_id_o         = 1'b0;
    csr_save_wb_o         = 1'b0;
    csr_restore_mret_id_o = 1'b0;
    csr_restore_dret_id_o = 1'b0;
    csr_save_cause_o      = 1'b0;
    csr_mtval_o           = '0;

    // The values of pc_mux and exc_pc_mux are only relevant if pc_set is set. Some of the states
    // below always set pc_mux and exc_pc_mux but only set pc_set if certain conditions are met.
    // This avoid having to factor those conditions into the pc_mux and exc_pc_mux select signals
    // helping timing.
    pc_mux_o               = PC_BOOT;
    pc_set_o               = 1'b0;
    pc_set_spec_o          = 1'b0;
    nt_branch_mispredict_o = 1'b0;

    exc_pc_mux_o           = EXC_PC_IRQ;
    exc_cause_o            = EXC_CAUSE_INSN_ADDR_MISA; // = 6'h00

    ctrl_fsm_ns            = ctrl_fsm_cs;

    ctrl_busy_o            = 1'b1;

    halt_if                = 1'b0;
    retain_id              = 1'b0;
    flush_id               = 1'b0;

    debug_csr_save_o       = 1'b0;
    debug_cause_o          = DBG_CAUSE_EBREAK;
    debug_mode_d           = debug_mode_q;
    nmi_mode_d             = nmi_mode_q;

    perf_tbranch_o         = 1'b0;
    perf_jump_o            = 1'b0;

    controller_run_o       = 1'b0;

    unique case (ctrl_fsm_cs)
      RESET: begin
        instr_req_o   = 1'b0;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        pc_set_spec_o = 1'b1;
        ctrl_fsm_ns   = BOOT_SET;
      end

      BOOT_SET: begin
        // copy boot address to instr fetch address
        instr_req_o   = 1'b1;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        pc_set_spec_o = 1'b1;

        ctrl_fsm_ns = FIRST_FETCH;
      end

      WAIT_SLEEP: begin
        ctrl_busy_o   = 1'b0;
        instr_req_o   = 1'b0;
        halt_if       = 1'b1;
        flush_id      = 1'b1;
        ctrl_fsm_ns   = SLEEP;
      end

      SLEEP: begin
        // instruction in IF stage is already valid
        // we begin execution when an interrupt has arrived
        instr_req_o   = 1'b0;
        halt_if       = 1'b1;
        flush_id      = 1'b1;

        // normal execution flow
        // in debug mode or single step mode we leave immediately (wfi=nop)
        if (irq_nm_i || irq_pending_i || debug_req_i || debug_mode_q || debug_single_step_i) begin
          ctrl_fsm_ns = FIRST_FETCH;
        end else begin
          // Make sure clock remains disabled.
          ctrl_busy_o = 1'b0;
        end
      end

      FIRST_FETCH: begin
        // Stall because of IF miss
        if (id_in_ready_o) begin
          ctrl_fsm_ns = DECODE;
        end

        // handle interrupts
        if (handle_irq) begin
          // We are handling an interrupt. Set halt_if to tell IF not to give
          // us any more instructions before it redirects to the handler, but
          // don't set flush_id: we must allow this instruction to complete
          // (since it might have outstanding loads or stores).
          ctrl_fsm_ns = IRQ_TAKEN;
          halt_if     = 1'b1;
        end

        // enter debug mode
        if (enter_debug_mode) begin
          ctrl_fsm_ns = DBG_TAKEN_IF;
          // Halt IF only for now, ID will be flushed in DBG_TAKEN_IF as the
          // ID state is needed for correct debug mode entry
          halt_if     = 1'b1;
        end
      end

      DECODE: begin
        // normal operating mode of the ID stage, in case of debug and interrupt requests,
        // priorities are as follows (lower number == higher priority)
        // 1. currently running (multicycle) instructions and exceptions caused by these
        // 2. debug requests
        // 3. interrupt requests

        controller_run_o = 1'b1;

        // Set PC mux for branch and jump here to ease timing. Value is only relevant if pc_set_o is
        // also set. Setting the mux value here avoids factoring in special_req and instr_valid_i
        // which helps timing.
        pc_mux_o = PC_JUMP;


        // Get ready for special instructions, exceptions, pipeline flushes
        if (special_req_all) begin
          // Halt IF but don't flush ID. This leaves a valid instruction in
          // ID so controller can determine appropriate action in the
          // FLUSH state.
          retain_id = 1'b1;

          // Wait for the writeback stage to either be ready for a new instruction or raise its own
          // exception before going to FLUSH. If the instruction in writeback raises an exception it
          // must take priority over any exception from an instruction in ID/EX. Only once the
          // writeback stage is ready can we be certain that won't happen. Without a writeback
          // stage ready_wb_i == 1 so the FSM will always go directly to FLUSH.

          if (ready_wb_i | wb_exception_o) begin
            ctrl_fsm_ns = FLUSH;
          end
        end

        if (!special_req_branch) begin
          if (branch_set_i || jump_set_i) begin
            // Only set the PC if the branch predictor hasn't already done the branch for us
            pc_set_o       = BranchPredictor ? ~instr_bp_taken_i : 1'b1;

            perf_tbranch_o = branch_set_i;
            perf_jump_o    = jump_set_i;
          end

          if (BranchPredictor) begin
            if (instr_bp_taken_i & branch_not_set_i) begin
              // If the instruction is a branch that was predicted to be taken but was not taken
              // signal a mispredict.
              nt_branch_mispredict_o = 1'b1;
            end
          end
        end

        // pc_set signal excluding branch taken condition
        if ((branch_set_spec_i || jump_set_i) && !special_req_branch) begin
          // Only speculatively set the PC if the branch predictor hasn't already done the branch
          // for us
          pc_set_spec_o = BranchPredictor ? ~instr_bp_taken_i : 1'b1;
        end

        // If entering debug mode or handling an IRQ the core needs to wait
        // until the current instruction has finished executing. Stall IF
        // during that time.
        if ((enter_debug_mode || handle_irq) && stall) begin
          halt_if = 1'b1;
        end

        if (!stall && !special_req_all) begin
          if (enter_debug_mode) begin
            // enter debug mode
            ctrl_fsm_ns = DBG_TAKEN_IF;
            // Halt IF only for now, ID will be flushed in DBG_TAKEN_IF as the
            // ID state is needed for correct debug mode entry
            halt_if     = 1'b1;
          end else if (handle_irq) begin
            // handle interrupt (not in debug mode)
            ctrl_fsm_ns = IRQ_TAKEN;
            // We are handling an interrupt (not in debug mode). Set halt_if to
            // tell IF not to give us any more instructions before it redirects
            // to the handler, but don't set flush_id: we must allow this
            // instruction to complete (since it might have outstanding loads
            // or stores).
            halt_if     = 1'b1;
          end
        end

      end // DECODE

      IRQ_TAKEN: begin
        pc_mux_o     = PC_EXC;
        exc_pc_mux_o = EXC_PC_IRQ;

        if (handle_irq) begin
          pc_set_o         = 1'b1;
          pc_set_spec_o    = 1'b1;

          csr_save_if_o    = 1'b1;
          csr_save_cause_o = 1'b1;

          // interrupt priorities according to Privileged Spec v1.11 p.31
          if (irq_nm_i && !nmi_mode_q) begin
            exc_cause_o = EXC_CAUSE_IRQ_NM;
            nmi_mode_d  = 1'b1; // enter NMI mode
          end else if (irqs_i.irq_fast != 15'b0) begin
            // generate exception cause ID from fast interrupt ID:
            // - first bit distinguishes interrupts from exceptions,
            // - second bit adds 16 to fast interrupt ID
            // for example EXC_CAUSE_IRQ_FAST_0 = {1'b1, 5'd16}
            exc_cause_o = exc_cause_e'({2'b11, mfip_id});
          end else if (irqs_i.irq_external) begin
            exc_cause_o = EXC_CAUSE_IRQ_EXTERNAL_M;
          end else if (irqs_i.irq_software) begin
            exc_cause_o = EXC_CAUSE_IRQ_SOFTWARE_M;
          end else begin // irqs_i.irq_timer
            exc_cause_o = EXC_CAUSE_IRQ_TIMER_M;
          end
        end

        ctrl_fsm_ns = DECODE;
      end

      DBG_TAKEN_IF: begin
        pc_mux_o     = PC_EXC;
        exc_pc_mux_o = EXC_PC_DBD;

        // enter debug mode and save PC in IF to dpc
        // jump to debug exception handler in debug memory
        if (debug_single_step_i || debug_req_i || trigger_match_i) begin
          flush_id         = 1'b1;
          pc_set_o         = 1'b1;
          pc_set_spec_o    = 1'b1;

          csr_save_if_o    = 1'b1;
          debug_csr_save_o = 1'b1;

          csr_save_cause_o = 1'b1;
          if (trigger_match_i) begin
            debug_cause_o = DBG_CAUSE_TRIGGER;
          end else if (debug_single_step_i) begin
            debug_cause_o = DBG_CAUSE_STEP;
          end else begin
            debug_cause_o = DBG_CAUSE_HALTREQ;
          end

          // enter debug mode
          debug_mode_d = 1'b1;
        end

        ctrl_fsm_ns  = DECODE;
      end

      DBG_TAKEN_ID: begin
        // enter debug mode and save PC in ID to dpc, used when encountering
        // 1. EBREAK during debug mode
        // 2. EBREAK with forced entry into debug mode (ebreakm or ebreaku set).
        // regular ebreak's go through FLUSH.
        //
        // for 1. do not update dcsr and dpc, for 2. do so [Debug Spec v0.13.2, p.39]
        // jump to debug exception handler in debug memory
        flush_id      = 1'b1;
        pc_mux_o      = PC_EXC;
        pc_set_o      = 1'b1;
        pc_set_spec_o = 1'b1;
        exc_pc_mux_o  = EXC_PC_DBD;

        // update dcsr and dpc
        if (ebreak_into_debug && !debug_mode_q) begin // ebreak with forced entry

          // dpc (set to the address of the EBREAK, i.e. set to PC in ID stage)
          csr_save_cause_o = 1'b1;
          csr_save_id_o    = 1'b1;

          // dcsr
          debug_csr_save_o = 1'b1;
          debug_cause_o    = DBG_CAUSE_EBREAK;
        end

        // enter debug mode
        debug_mode_d = 1'b1;

        ctrl_fsm_ns  = DECODE;
      end

      FLUSH: begin
        // flush the pipeline
        halt_if     = 1'b1;
        flush_id    = 1'b1;
        ctrl_fsm_ns = DECODE;

        // As pc_mux and exc_pc_mux can take various values in this state they aren't set early
        // here.

        // exceptions: set exception PC, save PC and exception cause
        // exc_req_lsu is high for one clock cycle only (in DECODE)
        if (exc_req_q || store_err_q || load_err_q) begin
          pc_set_o         = 1'b1;
          pc_set_spec_o    = 1'b1;
          pc_mux_o         = PC_EXC;
          exc_pc_mux_o     = debug_mode_q ? EXC_PC_DBG_EXC : EXC_PC_EXC;

          if (WritebackStage) begin : g_writeback_mepc_save
            // With the writeback stage present whether an instruction accessing memory will cause
            // an exception is only known when it is in writeback. So when taking such an exception
            // epc must come from writeback.
            csr_save_id_o  = ~(store_err_q | load_err_q);
            csr_save_wb_o  = store_err_q | load_err_q;
          end else begin : g_no_writeback_mepc_save
            csr_save_id_o  = 1'b0;
          end

          csr_save_cause_o = 1'b1;

          // Exception/fault prioritisation logic will have set exactly 1 X_prio signal
          unique case (1'b1)
            instr_fetch_err_prio: begin
                exc_cause_o = EXC_CAUSE_INSTR_ACCESS_FAULT;
                csr_mtval_o = instr_fetch_err_plus2_i ? (pc_id_i + 32'd2) : pc_id_i;
            end
            illegal_insn_prio: begin
              exc_cause_o = EXC_CAUSE_ILLEGAL_INSN;
              csr_mtval_o = instr_is_compressed_i ? {16'b0, instr_compressed_i} : instr_i;
            end
            ecall_insn_prio: begin
              exc_cause_o = (priv_mode_i == PRIV_LVL_M) ? EXC_CAUSE_ECALL_MMODE :
                                                          EXC_CAUSE_ECALL_UMODE;
            end
            ebrk_insn_prio: begin
              if (debug_mode_q | ebreak_into_debug) begin
                /*
                 * EBREAK in debug mode re-enters debug mode
                 *
                 * "The only exception is EBREAK. When that is executed in Debug
                 * Mode, it halts the hart again but without updating dpc or
                 * dcsr." [Debug Spec v0.13.2, p.39]
                 */

                /*
                 * dcsr.ebreakm == 1:
                 * "EBREAK instructions in M-mode enter Debug Mode."
                 * [Debug Spec v0.13.2, p.42]
                 */
                pc_set_o         = 1'b0;
                pc_set_spec_o    = 1'b0;
                csr_save_id_o    = 1'b0;
                csr_save_cause_o = 1'b0;
                ctrl_fsm_ns      = DBG_TAKEN_ID;
                flush_id         = 1'b0;
              end else begin
                /*
                 * "The EBREAK instruction is used by debuggers to cause control
                 * to be transferred back to a debugging environment. It
                 * generates a breakpoint exception and performs no other
                 * operation. [...] ECALL and EBREAK cause the receiving
                 * privilege mode's epc register to be set to the address of the
                 * ECALL or EBREAK instruction itself, not the address of the
                 * following instruction." [Privileged Spec v1.11, p.40]
                 */
                exc_cause_o      = EXC_CAUSE_BREAKPOINT;
              end
            end
            store_err_prio: begin
              exc_cause_o = EXC_CAUSE_STORE_ACCESS_FAULT;
              csr_mtval_o = lsu_addr_last_i;
            end
            load_err_prio: begin
              exc_cause_o = EXC_CAUSE_LOAD_ACCESS_FAULT;
              csr_mtval_o = lsu_addr_last_i;
            end
            default: ;
          endcase
        end else begin
          // special instructions and pipeline flushes
          if (mret_insn) begin
            pc_mux_o              = PC_ERET;
            pc_set_o              = 1'b1;
            pc_set_spec_o         = 1'b1;
            csr_restore_mret_id_o = 1'b1;
            if (nmi_mode_q) begin
              nmi_mode_d          = 1'b0; // exit NMI mode
            end
          end else if (dret_insn) begin
            pc_mux_o              = PC_DRET;
            pc_set_o              = 1'b1;
            pc_set_spec_o         = 1'b1;
            debug_mode_d          = 1'b0;
            csr_restore_dret_id_o = 1'b1;
          end else if (wfi_insn) begin
            ctrl_fsm_ns           = WAIT_SLEEP;
          end else if (csr_pipe_flush && handle_irq) begin
            // start handling IRQs when doing CSR-related pipeline flushes
            ctrl_fsm_ns           = IRQ_TAKEN;
          end
        end // exc_req_q

        // Entering debug mode due to either single step or debug_req. Ensure
        // registers are set for exception but then enter debug handler rather
        // than exception handler [Debug Spec v0.13.2, p.44]
        // Leave all other signals as is to ensure CSRs and PC get set as if
        // core was entering exception handler, entry to debug mode will then
        // see the appropriate state and setup dpc correctly.
        // If an EBREAK instruction is causing us to enter debug mode on the
        // same cycle as a debug_req or single step, honor the EBREAK and
        // proceed to DBG_TAKEN_ID.
        if (enter_debug_mode && !(ebrk_insn_prio && ebreak_into_debug)) begin
          ctrl_fsm_ns = DBG_TAKEN_IF;
        end
      end // FLUSH

      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = RESET;
      end
    endcase
  end

  assign flush_id_o = flush_id;

  // signal to CSR when in debug mode
  assign debug_mode_o = debug_mode_q;

  // signal to CSR when in an NMI handler (for nested exception handling)
  assign nmi_mode_o = nmi_mode_q;

  ///////////////////
  // Stall control //
  ///////////////////

  // If high current instruction cannot complete this cycle. Either because it needs more cycles to
  // finish (stall_id_i) or because the writeback stage cannot accept it yet (stall_wb_i). If there
  // is no writeback stage stall_wb_i is a constant 0.
  assign stall = stall_id_i | stall_wb_i;

  // signal to IF stage that ID stage is ready for next instr
  assign id_in_ready_o = ~stall & ~halt_if & ~retain_id;

  // kill instr in IF-ID pipeline reg that are done, or if a
  // multicycle instr causes an exception for example
  // retain_id is another kind of stall, where the instr_valid bit must remain
  // set (unless flush_id is set also). It cannot be factored directly into
  // stall as this causes a combinational loop.
  assign instr_valid_clear_o = ~(stall | retain_id) | flush_id;

  // update registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : update_regs
    if (!rst_ni) begin
      ctrl_fsm_cs    <= RESET;
      nmi_mode_q     <= 1'b0;
      debug_mode_q   <= 1'b0;
      load_err_q     <= 1'b0;
      store_err_q    <= 1'b0;
      exc_req_q      <= 1'b0;
      illegal_insn_q <= 1'b0;
    end else begin
      ctrl_fsm_cs    <= ctrl_fsm_ns;
      nmi_mode_q     <= nmi_mode_d;
      debug_mode_q   <= debug_mode_d;
      load_err_q     <= load_err_d;
      store_err_q    <= store_err_d;
      exc_req_q      <= exc_req_d;
      illegal_insn_q <= illegal_insn_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(AlwaysInstrClearOnMispredict, nt_branch_mispredict_o -> instr_valid_clear_o)

  // Selectors must be known/valid.
  `ASSERT(IbexCtrlStateValid, ctrl_fsm_cs inside {
      RESET, BOOT_SET, WAIT_SLEEP, SLEEP, FIRST_FETCH, DECODE, FLUSH,
      IRQ_TAKEN, DBG_TAKEN_IF, DBG_TAKEN_ID})

  // The speculative branch signal should be set whenever the actual branch signal is set
  `ASSERT(IbexSpecImpliesSetPC, pc_set_o |-> pc_set_spec_o)

endmodule
