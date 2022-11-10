// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_bind;

  // This is bound directly to top_earlgrey since neither pwrmgr nor rstmgr see all necessary
  // signals.
  bind top_earlgrey pwrmgr_rstmgr_sva_if pwrmgr_rstmgr_sva_if (
    .clk_i(u_pwrmgr_aon.clk_i),
    .rst_ni(u_pwrmgr_aon.rst_ni),
    .clk_slow_i(u_pwrmgr_aon.clk_slow_i),
    .rst_slow_ni(u_pwrmgr_aon.rst_slow_ni),
    // Input resets.
    .rstreqs_i(u_pwrmgr_aon.rstreqs_i),
    .reset_en(u_pwrmgr_aon.reg2hw.reset_en),
    .sw_rst_req_i(prim_mubi_pkg::mubi4_test_true_strict(u_pwrmgr_aon.sw_rst_req_i)),
    .main_rst_req_i(!u_pwrmgr_aon.rst_main_ni),
    .esc_rst_req_i(u_pwrmgr_aon.esc_rst_req_q),
    // The outputs from pwrmgr.
    .rst_lc_req(u_pwrmgr_aon.pwr_rst_o.rst_lc_req),
    .rst_sys_req(u_pwrmgr_aon.pwr_rst_o.rst_sys_req),
    .rstreqs(u_pwrmgr_aon.pwr_rst_o.rstreqs),
    .main_pd_n(u_pwrmgr_aon.pwr_ast_o.main_pd_n),
    .reset_cause(u_pwrmgr_aon.pwr_rst_o.reset_cause),
    // This goes directly to rstmgr and can trigger rst_sys_src_n.
    .ndm_sys_req(u_rstmgr_aon.ndmreset_req_i),
    // The inputs from rstmgr.
    .rst_lc_src_n(u_pwrmgr_aon.pwr_rst_i.rst_lc_src_n),
    .rst_sys_src_n(u_pwrmgr_aon.pwr_rst_i.rst_sys_src_n)
  );

  bind top_earlgrey pwrmgr_ast_sva_if #(
    .CheckClocks(1'b1)
  ) pwrmgr_ast_sva_if (
    .clk_slow_i(u_pwrmgr_aon.clk_slow_i),
    .rst_slow_ni(u_pwrmgr_aon.rst_slow_ni),
    .clk_main_i(u_clkmgr_aon.clk_main_i),
    .clk_io_i(u_clkmgr_aon.clk_io_i),
    .clk_usb_i(u_clkmgr_aon.clk_usb_i),
    .por_d0_ni(por_n_i[1]),
    // The pwrmgr outputs.
    .pwr_ast_o(u_pwrmgr_aon.pwr_ast_o),
    // The pwrmgr input.
    .pwr_ast_i(u_pwrmgr_aon.pwr_ast_i)
  );

  logic [ibex_pkg::IC_NUM_WAYS-1:0]                     ibex_icache_tag_bank_key_valid,
                                                        ibex_icache_data_bank_key_valid;
  otp_ctrl_pkg::sram_key_t [ibex_pkg::IC_NUM_WAYS-1:0]  ibex_icache_tag_bank_key,
                                                        ibex_icache_data_bank_key;
  bind top_earlgrey rv_core_ibex_otp_sva_if #(
    .ICache(u_rv_core_ibex.ICache),
    .ICacheScramble(u_rv_core_ibex.ICacheScramble)
  ) rv_core_ibex_otp_sva_if (
    .ibex_decoder_instr_valid(u_rv_core_ibex.u_core.u_ibex_core.id_stage_i.instr_valid_i),
    .ibex_decoder_instr(u_rv_core_ibex.u_core.u_ibex_core.id_stage_i.decoder_i.instr),
    .ibex_decoder_opcode(u_rv_core_ibex.u_core.u_ibex_core.id_stage_i.decoder_i.opcode),
    .ibex_icache_tag_bank_key_valid(ibex_icache_tag_bank_key_valid),
    .ibex_icache_tag_bank_key(ibex_icache_tag_bank_key),
    .ibex_icache_data_bank_key_valid(ibex_icache_data_bank_key_valid),
    .ibex_icache_data_bank_key(ibex_icache_data_bank_key),
    .otp_sram_otp_key_i_req(u_otp_ctrl.sram_otp_key_i.req),
    .otp_sram_otp_key_o_ack(u_otp_ctrl.sram_otp_key_o.ack),
    .otp_sram_otp_key_o_key(u_otp_ctrl.sram_otp_key_o.key)
  );
  for (genvar way = 0; way < ibex_pkg::IC_NUM_WAYS; way++) begin : gen_icache_ways
    assign ibex_icache_tag_bank_key_valid[way] =
        u_rv_core_ibex.u_core.gen_rams.gen_rams_inner[way].gen_scramble_rams.tag_bank.key_valid_i;
    assign ibex_icache_data_bank_key_valid[way] =
        u_rv_core_ibex.u_core.gen_rams.gen_rams_inner[way].gen_scramble_rams.data_bank.key_valid_i;
    assign ibex_icache_tag_bank_key[way] =
        u_rv_core_ibex.u_core.gen_rams.gen_rams_inner[way].gen_scramble_rams.tag_bank.key_i;
    assign ibex_icache_data_bank_key[way] =
        u_rv_core_ibex.u_core.gen_rams.gen_rams_inner[way].gen_scramble_rams.data_bank.key_i;
  end

endmodule
