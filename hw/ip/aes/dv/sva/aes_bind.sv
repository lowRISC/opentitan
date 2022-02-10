// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module aes_bind;

  bind aes tlul_assert #(
    .EndpointType("Device")
  )  tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind aes aes_csr_assert_fpv aes_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );

  bind aes aes_idle_check idle_check (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),
    .reg2hw   (reg2hw),
    .idle_i   (idle_o)
  );

  bind aes aes_reseed_if u_aes_reseed_if (
    .clk_i                 (clk_i),
    .rst_ni                (rst_ni),
    .entropy_clearing_req  (entropy_clearing_req),
    .entropy_clearing_ack  (entropy_clearing_ack),
    .entropy_masking_req   (entropy_masking_req),
    .entropy_masking_ack   (entropy_masking_ack),
    .prng_reseed_rate      (u_aes_core.prng_reseed_rate_q),
    .entropy_req_o         (u_aes_core.u_aes_prng_clearing.entropy_req_o),
    .entropy_ack_i         (u_aes_core.u_aes_prng_clearing.entropy_ack_i),
    .seed_en               (u_aes_core.u_aes_prng_clearing.seed_en),
    .entropy_i             (u_aes_core.u_aes_prng_clearing.entropy_i),
    .buffer_q              (u_aes_core.u_aes_prng_clearing.gen_buffer.buffer_q),
    .lfsr_q                (u_aes_core.u_aes_prng_clearing.u_lfsr.lfsr_q),
    .ctrl_phase_i          (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                            u_aes_control_fsm.ctrl_phase_i),
    .ctrl_we_q             (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                            u_aes_control_fsm.ctrl_we_q),
    .block_ctr_decr        (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                            u_aes_control_fsm.block_ctr_decr),
    .block_ctr_expr        (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                            u_aes_control_fsm.block_ctr_expr)
  );

  bind aes_prng_masking aes_masking_reseed_if u_aes_masking_reseed_if (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .prng_seed_en (prng_seed_en),
    .prng_seed    (prng_seed),
    .lfsr_q_0     (gen_lfsrs[0].u_lfsr_chunk.lfsr_q),
    .lfsr_q_1     (gen_lfsrs[1].u_lfsr_chunk.lfsr_q),
    .lfsr_q_2     (gen_lfsrs[2].u_lfsr_chunk.lfsr_q),
    .lfsr_q_3     (gen_lfsrs[3].u_lfsr_chunk.lfsr_q),
    .lfsr_q_4     (gen_lfsrs[4].u_lfsr_chunk.lfsr_q)
  );
endmodule
