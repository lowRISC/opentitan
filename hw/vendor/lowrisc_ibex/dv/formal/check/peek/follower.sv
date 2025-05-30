// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following implements the pipeline follower. It is pretty simple since the pipeline is short.

The top of this file contains signals to indicate when an instruction moves from a pipeline stage,
and when it does so on what terms.

We record both the spec post state and the implementation CSR post state as soon as the instruction moves on from ID/EX.
The latter is stored so that we can make comparisons at the same time, independent of when the instruction retires. We
probably could do this earlier in the cases where no exception occurs, but that would require special treatment for
exception vs non-exception cases. In fairness there is already a difference, but that's only a case split which can be unified.
*/

`define INSTR `CR.instr_rdata_id

// These control signals are all extremely specific and probably very fragile.

assign ex_success = `ID.instr_done;
assign ex_err = `IDC.exc_req_d;
assign ex_kill = `ID.wb_exception | ~`ID.controller_run;
// Note that this only kills instructions because e.g. of a jump ahead of it or an exception

assign exc_finishing = `IDC.ctrl_fsm_cs == `ID.controller_i.FLUSH;
assign wbexc_handling_irq = `IDC.ctrl_fsm_cs == `ID.controller_i.IRQ_TAKEN;

assign wb_finishing = wbexc_is_wfi? wfi_will_finish:`CR.instr_done_wb;

assign wfi_will_finish = `IDC.ctrl_fsm_cs == `ID.controller_i.FLUSH;

assign wbexc_err =  wbexc_ex_err |
                    `IDC.wb_exception_o |
                    ((`IDC.ctrl_fsm_cs == `ID.controller_i.FLUSH) & ~wbexc_csr_pipe_flush);
                    // CSR pipe flushes don't count as exceptions

assign wbexc_finishing =
    wbexc_exists & (wbexc_err ? exc_finishing : wb_finishing);

assign instr_will_progress = (~wbexc_exists | wbexc_finishing) & ~ex_kill & (ex_success | ex_err);

always_comb begin
    if (`CR.instr_new_id) begin
        ex_has_branched_d = 1'b0;
    end else begin
        ex_has_branched_d = ex_has_branched_q;
    end

    ex_has_branched_d = (ex_has_branched_d | `IF.branch_req) &&
                        ~ex_kill &&
                        (`IDC.ctrl_fsm_cs == `IDC.DECODE);
end

always @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
        wbexc_exists <= 1'b0;
        ex_has_compressed_instr <= 1'b0;
        ex_has_branched_q <= 1'b0;
        wbexc_csr_pipe_flush <= 1'b0;
    end else begin
        if (wbexc_finishing) begin
            wbexc_exists <= 1'b0;
        end

        ex_has_branched_q <= ex_has_branched_d;
        if (instr_will_progress) begin
            ex_has_branched_q <= 1'b0;
            wbexc_post_wX <= spec_post_wX;
            wbexc_post_wX_addr <= spec_post_wX_addr;
            wbexc_post_wX_en <= spec_post_wX_en;

            `define X(n) wbexc_post_``n <= spec_post_``n;
            `X_EACH_CSR
            `undef X

            `define X(n) wbexc_dut_post_``n <= post_``n;
            `X_EACH_CSR
            `undef X

            wbexc_instr <= ex_compressed_instr;
            wbexc_decompressed_instr <= `CR.instr_rdata_id;
            wbexc_compressed_illegal <= `CR.illegal_c_insn_id;
            wbexc_exists <= 1'b1;
            wbexc_ex_err <= ex_err;
            wbexc_fetch_err <= `ID.instr_fetch_err_i;
            wbexc_post_int_err <= spec_int_err;
            wbexc_illegal <= `CR.illegal_insn_id;
            wbexc_pc <= `CR.pc_id;
            wbexc_csr_pipe_flush <= `IDC.csr_pipe_flush;
            wbexc_is_checkable_csr <= ex_is_checkable_csr;

            wbexc_spec_mem_read_fst_rdata <= spec_mem_read_fst_rdata;
            wbexc_spec_mem_read_snd_rdata <= spec_mem_read_snd_rdata;
            wbexc_mem_had_snd_req <= mem_gnt_snd_q | mem_gnt_snd_d;
        end

        if (`IF.if_id_pipe_reg_we) begin
            ex_compressed_instr <= `IF.if_instr_rdata;
            ex_has_compressed_instr <= 1'b1;
        end
    end
end

assign spec_en = wbexc_handling_irq | instr_will_progress;
// The definition of spec_en doesn't matter so long as it's live (which it is since
// instr will progress is live), so long as the necessary wraparound properties prove.

always @(posedge clk_i) begin
    if (~rst_ni) begin
        has_spec_past = 1'b0;
        spec_past_has_reg = 32'b0;
    end else if (spec_en) begin
        has_spec_past = `IS_CSR -> ex_is_checkable_csr;

        if (spec_post_wX_en) begin
            spec_past_regs[spec_post_wX_addr] = spec_post_wX;
            spec_past_has_reg[spec_post_wX_addr] = 1'b1;
        end
        if (`IS_CSR & ~ex_is_checkable_csr) begin
            // Clear out everything, since we don't know what has been written to any more
            // We could be stricter but there's little point in doing so.
            spec_past_has_reg = 32'b0;
        end

        `define X(n) spec_past_``n = spec_post_``n;
        `X_EACH_CSR
        `undef X
    end
 end

`undef INSTR
