// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following instantiates the specification via the spec api. It also chooses the mode for the spec to run in (see main.sail
for more on that).

It just wires up the pre_* state to the spec_post* state.
*/

t_MainMode main_mode;

always_comb begin
    if (wbexc_handling_irq) main_mode = MAIN_IRQ;
    else if (`ID.instr_fetch_err_i) main_mode = MAIN_IFERR;
    else main_mode = MAIN_IDEX;
end

spec_api #(
    .NREGS(32)
) spec_api_i (
    .int_err_o(spec_int_err),
    .main_mode(main_mode),

    .insn_bits(ex_compressed_instr),

    .rx_a_en_o(spec_rx_a_en),
    .rx_a_addr_o(spec_rx_a_addr),
    .rx_a_i(spec_rx_a),
    .rx_b_en_o(spec_rx_b_en),
    .rx_b_addr_o(spec_rx_b_addr),
    .rx_b_i(spec_rx_b),

    .wx_o(spec_post_wX),
    .wx_addr_o(spec_post_wX_addr),
    .wx_en_o(spec_post_wX_en),

    .mvendor_id_i(CSR_MVENDORID_VALUE),
    .march_id_i(CSR_MARCHID_VALUE),
    .mimp_id_i(CSR_MIMPID_VALUE),
    .mhart_id_i(hart_id_i),
    .mconfigptr_i(CSR_MCONFIGPTR_VALUE),

    .misa_i(`CSR.MISA_VALUE),
    .mip_i(pre_mip),
    .nextpc_i(pre_nextpc),

    `define X(n) .n``_i(pre_``n), .n``_o(spec_post_``n),
    `X_EACH_CSR
    `undef X

    .mem_read_o(spec_mem_read),
    .mem_read_snd_gran_o(spec_mem_read_snd),
    .mem_read_fst_addr_o(spec_mem_read_fst_addr),
    .mem_read_snd_addr_o(spec_mem_read_snd_addr),
    .mem_read_fst_rdata_i(spec_mem_read_fst_rdata),
    .mem_read_snd_rdata_i(spec_mem_read_snd_rdata),

    .mem_write_o(spec_mem_write),
    .mem_write_snd_gran_o(spec_mem_write_snd),
    .mem_write_fst_addr_o(spec_mem_write_fst_addr),
    .mem_write_snd_addr_o(spec_mem_write_snd_addr),
    .mem_write_fst_wdata_o(spec_mem_write_fst_wdata),
    .mem_write_snd_wdata_o(spec_mem_write_snd_wdata),
    .mem_write_fst_be_o(spec_mem_write_fst_be),
    .mem_write_snd_be_o(spec_mem_write_snd_be)
);
