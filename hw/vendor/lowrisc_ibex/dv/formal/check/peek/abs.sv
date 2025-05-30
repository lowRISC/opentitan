// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
This file implements the abstract state for Ibex, it maps Ibex microarchitectural state to Sail architectural state.
pre_* is the pre_state, i.e. if an instruction is starting to run now, this is the architectural state that it observes.
post_* is the post_state, i.e. if an instruction starts in the next cycle, this is the architectural state that it will observe.
If this is wrong it does not matter, due to the wrap around proofs.
*/

/////////////// GPR Pre-State ///////////////

assign pre_regs[0] = 32'h0;
for (genvar i = 1; i < 32; i++) begin: g_pre_regs
    // Resolve forwarding
    assign pre_regs[i] = (`CR.rf_write_wb && `CR.rf_waddr_wb == i) ?
                                    `CR.rf_wdata_fwd_wb : `RF.rf_reg[i];
end

// FIXME: Redefined from ibex_cs_registers
typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
    logic      mprv;
    logic      tw;
} status_t;

/////////////// CSR Pre-State ///////////////

assign pre_pc = wbexc_handling_irq? `CR.pc_if:`CR.pc_id;
assign pre_nextpc = `CR.pc_id + (`CR.instr_is_compressed_id ? 2 : 4);
assign pre_priv = `CSR.priv_lvl_q == PRIV_LVL_M ? Machine : User;
assign pre_mstatus = '{
    mie: `CSR.mstatus_q.mie,
    mpie: `CSR.mstatus_q.mpie,
    tw: `CSR.mstatus_q.tw,
    mprv: `CSR.mstatus_q.mprv,
    mpp: `CSR.mstatus_q.mpp
};
assign pre_mip = irqsToMInterrupts(`CSR.mip);
assign pre_mie = irqsToMInterrupts(`CSR.mie_q);
assign pre_mcause = widenMCause(`CSR.mcause_q);
assign pre_mtval = `CSR.mtval_q;
assign pre_mtvec = `CSR.mtvec_q;
assign pre_mscratch = `CSR.mscratch_q;
assign pre_mepc = `CSR.mepc_q;
assign pre_mcounteren = '0; // ibex hardwires to zero
assign pre_mseccfg = mseccfgToBits(`CSRP.pmp_mseccfg_q);
for (genvar i = 0; i < PMPNumRegions; i++) begin: g_pmp_pre
    assign pre_pmp_cfg[i] = pmpCfgToBits(`CSRP.pmp_cfg[i]);
    assign pre_pmp_addr[i] = `CSRP.pmp_addr[i];
end

/////////////// CSR Post-State ///////////////

// Bit 0 of fetch addr n is always cleared.
assign post_pc = `IF.branch_req ? {`IF.fetch_addr_n[31:1], 1'b0} : `CSR.pc_if_i;
assign post_mie = `CSR.mie_en ? irqsToMInterrupts(`CSR.mie_d) : pre_mie;
assign post_priv = `CSR.priv_lvl_d == PRIV_LVL_M ? Machine : User;
assign post_mstatus = `CSR.mstatus_en ? '{
    mie: `CSR.mstatus_d.mie,
    mpie: `CSR.mstatus_d.mpie,
    tw: `CSR.mstatus_d.tw,
    mprv: `CSR.mstatus_d.mprv,
    mpp: `CSR.mstatus_d.mpp
}:pre_mstatus;
assign post_mcause = `CSR.mcause_en ? widenMCause(`CSR.mcause_d) : pre_mcause;
assign post_mtval = `CSR.mtval_en ? `CSR.mtval_d : pre_mtval;
assign post_mtvec = `CSR.mtvec_en ? `CSR.mtvec_d : pre_mtvec;
assign post_mepc = `CSR.mepc_en ? `CSR.mepc_d : pre_mepc;
assign post_mscratch = `CSR.mscratch_en? `CSR.csr_wdata_int : pre_mscratch;
assign post_mcounteren = '0;
assign post_mseccfg = `CSRP.pmp_mseccfg_we ? mseccfgToBits(`CSRP.pmp_mseccfg_d) : pre_mseccfg;
for (genvar i = 0; i < PMPNumRegions; i++) begin: g_pmp_post
    assign post_pmp_cfg[i] =
        `CSRP.pmp_cfg_we[i] ? pmpCfgToBits(`CSRP.pmp_cfg_wdata[i]) : pre_pmp_cfg[i];
    assign post_pmp_addr[i] = `CSRP.pmp_addr_we[i] ? `CSR.csr_wdata_int : pre_pmp_addr[i];
end

/////////////// Encoders ///////////////

function automatic logic [7:0] pmpCfgToBits(pmp_cfg_t cfg);
    return {cfg.lock, 2'b0, cfg.mode, cfg.exec, cfg.write, cfg.read};
endfunction

function automatic logic [31:0] mseccfgToBits(pmp_mseccfg_t mseccfg);
  return {29'h0, mseccfg.rlb, mseccfg.mmwp, mseccfg.mml};
endfunction

function automatic logic [31:0] irqsToMInterrupts(irqs_t irqs);
    // Sail has no notion of fast interrupts
    return
        (32'(irqs.irq_software) << 3) |
        (32'(irqs.irq_timer) << 7) |
        (32'(irqs.irq_external) << 11);
endfunction

function automatic logic[31:0] widenMCause(exc_cause_t mcause);
    // Intneral exceptions are not specified, maybe we should just ignore them?
    return {mcause.irq_ext | mcause.irq_int,
            mcause.irq_int ? {26{1'b1}} : 26'b0,
            mcause.lower_cause[4:0]};
endfunction
