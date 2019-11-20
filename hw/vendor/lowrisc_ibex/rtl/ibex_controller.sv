// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Main controller of the processor
 */
module ibex_controller (
    input  logic                  clk_i,
    input  logic                  rst_ni,

    input  logic                  fetch_enable_i,        // start decoding
    output logic                  ctrl_busy_o,           // core is busy processing instrs

    // decoder related signals
    input  logic                  illegal_insn_i,        // decoder has an invalid instr
    input  logic                  ecall_insn_i,          // decoder has ECALL instr
    input  logic                  mret_insn_i,           // decoder has MRET instr
    input  logic                  dret_insn_i,           // decoder has DRET instr
    input  logic                  wfi_insn_i,            // decoder has WFI instr
    input  logic                  ebrk_insn_i,           // decoder has EBREAK instr
    input  logic                  csr_pipe_flush_i,      // do CSR-related pipeline flush

    // from IF-ID pipeline stage
    input  logic                  instr_valid_i,         // instr from IF-ID reg is valid
    input  logic [31:0]           instr_i,               // instr from IF-ID reg, for mtval
    input  logic [15:0]           instr_compressed_i,    // instr from IF-ID reg, for mtval
    input  logic                  instr_is_compressed_i, // instr from IF-ID reg is compressed
    input  logic                  instr_fetch_err_i,     // instr from IF-ID reg has error
    input  logic [31:0]           pc_id_i,               // instr from IF-ID reg address

    // to IF-ID pipeline stage
    output logic                  instr_valid_clear_o,   // kill instr in IF-ID reg
    output logic                  id_in_ready_o,         // ID stage is ready for new instr

    // to prefetcher
    output logic                  instr_req_o,           // start fetching instructions
    output logic                  pc_set_o,              // jump to address set by pc_mux
    output ibex_pkg::pc_sel_e     pc_mux_o,              // IF stage fetch address selector
                                                         // (boot, normal, exception...)
    output ibex_pkg::exc_pc_sel_e exc_pc_mux_o,          // IF stage selector for exception PC
    output ibex_pkg::exc_cause_e  exc_cause_o,           // for IF stage, CSRs

    // LSU
    input  logic [31:0]           lsu_addr_last_i,       // for mtval
    input  logic                  load_err_i,
    input  logic                  store_err_i,

    // jump/branch signals
    input  logic                  branch_set_i,          // branch taken set signal
    input  logic                  jump_set_i,            // jump taken set signal

    // interrupt signals
    input  logic                  csr_mstatus_mie_i,     // M-mode interrupt enable bit
    input  logic                  csr_msip_i,            // software interrupt pending
    input  logic                  csr_mtip_i,            // timer interrupt pending
    input  logic                  csr_meip_i,            // external interrupt pending
    input  logic [14:0]           csr_mfip_i,            // fast interrupt pending
    input  logic                  irq_pending_i,         // interrupt request pending
    input  logic                  irq_nm_i,              // non-maskeable interrupt

    // debug signals
    input  logic                  debug_req_i,
    output ibex_pkg::dbg_cause_e  debug_cause_o,
    output logic                  debug_csr_save_o,
    output logic                  debug_mode_o,
    input  logic                  debug_single_step_i,
    input  logic                  debug_ebreakm_i,
    input  logic                  debug_ebreaku_i,

    output logic                  csr_save_if_o,
    output logic                  csr_save_id_o,
    output logic                  csr_restore_mret_id_o,
    output logic                  csr_restore_dret_id_o,
    output logic                  csr_save_cause_o,
    output logic [31:0]           csr_mtval_o,
    input  ibex_pkg::priv_lvl_e   priv_mode_i,
    input  logic                  csr_mstatus_tw_i,

    // stall signals
    input  logic                  stall_lsu_i,
    input  logic                  stall_multdiv_i,
    input  logic                  stall_jump_i,
    input  logic                  stall_branch_i,

    // performance monitors
    output logic                  perf_jump_o,           // we are executing a jump
                                                         // instruction (j, jr, jal, jalr)
    output logic                  perf_tbranch_o         // we are executing a taken branch
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

  logic stall;
  logic halt_if;
  logic flush_id;
  logic illegal_dret;
  logic illegal_umode;
  logic exc_req_lsu;
  logic special_req;
  logic enter_debug_mode;
  logic ebreak_into_debug;
  logic handle_irq;

  logic [3:0] mfip_id;
  logic       unused_csr_mtip;

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
  assign illegal_insn_d = (illegal_insn_i | illegal_dret | illegal_umode) & (ctrl_fsm_cs != FLUSH);

  // exception requests
  // requests are flopped in exc_req_q.  This is cleared when controller is in
  // the FLUSH state so the cycle following exc_req_q won't remain set for an
  // exception request that has just been handled.
  assign exc_req_d = (ecall_insn | ebrk_insn | illegal_insn_d | instr_fetch_err) &
                     (ctrl_fsm_cs != FLUSH);

  // LSU exception requests
  assign exc_req_lsu = store_err_i | load_err_i;

  // special requests: special instructions, pipeline flushes, exceptions...
  assign special_req = mret_insn | dret_insn | wfi_insn | csr_pipe_flush |
      exc_req_d | exc_req_lsu;

  ////////////////
  // Interrupts //
  ////////////////

  // Enter debug mode due to an external debug_req_i or because the core is in
  // single step mode (dcsr.step == 1). Single step must be qualified with
  // instruction valid otherwise the core will immediately enter debug mode
  // due to a recently flushed IF (or a delay in an instruction returning from
  // memory) before it has had anything to single step.
  assign enter_debug_mode = (debug_req_i | (debug_single_step_i & instr_valid_i)) & ~debug_mode_q;

  // Set when an ebreak should enter debug mode rather than jump to exception
  // handler
  assign ebreak_into_debug = priv_mode_i == PRIV_LVL_M ? debug_ebreakm_i :
                             priv_mode_i == PRIV_LVL_U ? debug_ebreaku_i :
                                                         1'b0;

  // interrupts including NMI are ignored while in debug mode [Debug Spec v0.13.2, p.39]
  assign handle_irq       = ~debug_mode_q &
      ((irq_nm_i & ~nmi_mode_q) | (irq_pending_i & csr_mstatus_mie_i));

  // generate ID of fast interrupts, highest priority to highest ID
  always_comb begin : gen_mfip_id
    if      (csr_mfip_i[14]) mfip_id = 4'd14;
    else if (csr_mfip_i[13]) mfip_id = 4'd13;
    else if (csr_mfip_i[12]) mfip_id = 4'd12;
    else if (csr_mfip_i[11]) mfip_id = 4'd11;
    else if (csr_mfip_i[10]) mfip_id = 4'd10;
    else if (csr_mfip_i[ 9]) mfip_id = 4'd9;
    else if (csr_mfip_i[ 8]) mfip_id = 4'd8;
    else if (csr_mfip_i[ 7]) mfip_id = 4'd7;
    else if (csr_mfip_i[ 6]) mfip_id = 4'd6;
    else if (csr_mfip_i[ 5]) mfip_id = 4'd5;
    else if (csr_mfip_i[ 5]) mfip_id = 4'd5;
    else if (csr_mfip_i[ 4]) mfip_id = 4'd4;
    else if (csr_mfip_i[ 3]) mfip_id = 4'd3;
    else if (csr_mfip_i[ 2]) mfip_id = 4'd2;
    else if (csr_mfip_i[ 1]) mfip_id = 4'd1;
    else                     mfip_id = 4'd0;
  end

  assign unused_csr_mtip = csr_mtip_i;

  /////////////////////
  // Core controller //
  /////////////////////

  always_comb begin
    // Default values
    instr_req_o           = 1'b1;

    csr_save_if_o         = 1'b0;
    csr_save_id_o         = 1'b0;
    csr_restore_mret_id_o = 1'b0;
    csr_restore_dret_id_o = 1'b0;
    csr_save_cause_o      = 1'b0;
    csr_mtval_o           = '0;

    pc_mux_o              = PC_BOOT;
    pc_set_o              = 1'b0;

    exc_pc_mux_o          = EXC_PC_IRQ;
    exc_cause_o           = EXC_CAUSE_INSN_ADDR_MISA; // = 6'h00

    ctrl_fsm_ns           = ctrl_fsm_cs;

    ctrl_busy_o           = 1'b1;

    halt_if               = 1'b0;
    flush_id              = 1'b0;

    debug_csr_save_o      = 1'b0;
    debug_cause_o         = DBG_CAUSE_EBREAK;
    debug_mode_d          = debug_mode_q;
    nmi_mode_d            = nmi_mode_q;

    perf_tbranch_o        = 1'b0;
    perf_jump_o           = 1'b0;

    unique case (ctrl_fsm_cs)
      RESET: begin
        // just wait for fetch_enable
        instr_req_o   = 1'b0;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;
        if (fetch_enable_i) begin
          ctrl_fsm_ns = BOOT_SET;
        end
      end

      BOOT_SET: begin
        // copy boot address to instr fetch address
        instr_req_o   = 1'b1;
        pc_mux_o      = PC_BOOT;
        pc_set_o      = 1'b1;

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
          // This assumes that the pipeline is always flushed before
          // going to sleep.
          ctrl_fsm_ns = IRQ_TAKEN;
          halt_if     = 1'b1;
          flush_id    = 1'b1;
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

        if (instr_valid_i) begin

          // get ready for special instructions, exceptions, pipeline flushes
          if (special_req) begin
            // Halt IF but don't flush ID. This leaves a valid instruction in
            // ID so controller can determine appropriate action in the
            // FLUSH state.
            ctrl_fsm_ns = FLUSH;
            halt_if     = 1'b1;
          // set PC in IF stage to branch or jump target
          end else if (branch_set_i || jump_set_i) begin
            pc_mux_o       = PC_JUMP;
            pc_set_o       = 1'b1;

            perf_tbranch_o = branch_set_i;
            perf_jump_o    = jump_set_i;
          end

          // If entering debug mode or handling an IRQ the core needs to wait
          // until the current instruction has finished executing. Stall IF
          // during that time.
          if ((enter_debug_mode || handle_irq) && stall) begin
            halt_if = 1'b1;
          end
        end // instr_valid_i

        if (!stall && !special_req) begin
          if (enter_debug_mode) begin
            // enter debug mode
            ctrl_fsm_ns = DBG_TAKEN_IF;
            // Halt IF only for now, ID will be flushed in DBG_TAKEN_IF as the
            // ID state is needed for correct debug mode entry
            halt_if     = 1'b1;
          end else if (handle_irq) begin
            // handle interrupt (not in debug mode)
            ctrl_fsm_ns = IRQ_TAKEN;
            halt_if     = 1'b1;
            flush_id    = 1'b1;
          end
        end

      end // DECODE

      IRQ_TAKEN: begin
        if (handle_irq) begin
          pc_mux_o         = PC_EXC;
          pc_set_o         = 1'b1;
          exc_pc_mux_o     = EXC_PC_IRQ;

          csr_save_if_o    = 1'b1;
          csr_save_cause_o = 1'b1;

          // interrupt priorities according to Privileged Spec v1.11 p.31
          if (irq_nm_i && !nmi_mode_q) begin
            exc_cause_o = EXC_CAUSE_IRQ_NM;
            nmi_mode_d  = 1'b1; // enter NMI mode
          end else if (csr_mfip_i != 15'b0) begin
            // generate exception cause ID from fast interrupt ID:
            // - first bit distinguishes interrupts from exceptions,
            // - second bit adds 16 to fast interrupt ID
            // for example EXC_CAUSE_IRQ_FAST_0 = {1'b1, 5'd16}
            exc_cause_o = exc_cause_e'({2'b11, mfip_id});
          end else if (csr_meip_i) begin
            exc_cause_o = EXC_CAUSE_IRQ_EXTERNAL_M;
          end else if (csr_msip_i) begin
            exc_cause_o = EXC_CAUSE_IRQ_SOFTWARE_M;
          end else begin // csr_mtip_i
            exc_cause_o = EXC_CAUSE_IRQ_TIMER_M;
          end
        end

        ctrl_fsm_ns = DECODE;
      end

      DBG_TAKEN_IF: begin
        // enter debug mode and save PC in IF to dpc
        // jump to debug exception handler in debug memory
        if (debug_single_step_i || debug_req_i) begin
          flush_id         = 1'b1;
          pc_mux_o         = PC_EXC;
          pc_set_o         = 1'b1;
          exc_pc_mux_o     = EXC_PC_DBD;

          csr_save_if_o    = 1'b1;
          debug_csr_save_o = 1'b1;

          csr_save_cause_o = 1'b1;
          if (debug_single_step_i) begin
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
        flush_id     = 1'b1;
        pc_mux_o     = PC_EXC;
        pc_set_o     = 1'b1;
        exc_pc_mux_o = EXC_PC_DBD;

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

        // exceptions: set exception PC, save PC and exception cause
        // exc_req_lsu is high for one clock cycle only (in DECODE)
        if (exc_req_q || store_err_q || load_err_q) begin
          pc_set_o         = 1'b1;
          pc_mux_o         = PC_EXC;
          exc_pc_mux_o     = debug_mode_q ? EXC_PC_DBG_EXC : EXC_PC_EXC;
          csr_save_id_o    = 1'b1;
          csr_save_cause_o = 1'b1;

          // set exception registers, priorities according to Table 3.7 of Privileged Spec v1.11
          if (instr_fetch_err) begin
            exc_cause_o = EXC_CAUSE_INSTR_ACCESS_FAULT;
            csr_mtval_o = pc_id_i;

          end else if (illegal_insn_q) begin
            exc_cause_o = EXC_CAUSE_ILLEGAL_INSN;
            csr_mtval_o = instr_is_compressed_i ? {16'b0, instr_compressed_i} : instr_i;

          end else if (ecall_insn) begin
            exc_cause_o = (priv_mode_i == PRIV_LVL_M) ? EXC_CAUSE_ECALL_MMODE :
                                                        EXC_CAUSE_ECALL_UMODE;

          end else if (ebrk_insn) begin
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

          end else if (store_err_q) begin
            exc_cause_o = EXC_CAUSE_STORE_ACCESS_FAULT;
            csr_mtval_o = lsu_addr_last_i;

          end else begin // load_err_q
            exc_cause_o = EXC_CAUSE_LOAD_ACCESS_FAULT;
            csr_mtval_o = lsu_addr_last_i;
          end

        end else begin
          // special instructions and pipeline flushes
          if (mret_insn) begin
            pc_mux_o              = PC_ERET;
            pc_set_o              = 1'b1;
            csr_restore_mret_id_o = 1'b1;
            if (nmi_mode_q) begin
              nmi_mode_d          = 1'b0; // exit NMI mode
            end
          end else if (dret_insn) begin
            pc_mux_o              = PC_DRET;
            pc_set_o              = 1'b1;
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
        if (enter_debug_mode) begin
          ctrl_fsm_ns = DBG_TAKEN_IF;
        end
      end // FLUSH

      default: begin
        instr_req_o = 1'b0;
        ctrl_fsm_ns = ctrl_fsm_e'(1'bX);
      end
    endcase
  end

  // signal to CSR when in debug mode
  assign debug_mode_o = debug_mode_q;

  ///////////////////
  // Stall control //
  ///////////////////

  // if high, current instr needs at least one more cycle to finish after the current cycle
  // if low, current instr finishes in current cycle
  // multicycle instructions have this set except during the last cycle
  assign stall = stall_lsu_i | stall_multdiv_i | stall_jump_i | stall_branch_i;

  // signal to IF stage that ID stage is ready for next instr
  assign id_in_ready_o       = ~stall & ~halt_if;

  // kill instr in IF-ID pipeline reg that are done, or if a
  // multicycle instr causes an exception for example
  // halt_if is another kind of stall, where the instr_valid bit must remain
  // set (unless flush_id is set also). It cannot be factored directly into
  // stall as this causes a combinational loop.
  assign instr_valid_clear_o = ~(stall | halt_if) | flush_id;

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

endmodule
