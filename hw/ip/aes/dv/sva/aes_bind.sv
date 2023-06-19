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
    .clk_i,
    .rst_ni,
    .entropy_clearing_req(entropy_clearing_req),
    .entropy_clearing_ack(entropy_clearing_ack),
    .entropy_i           (edn_data),
    .buffer_q            (u_aes_core.u_aes_prng_clearing.gen_buffer.buffer_q),
    .lfsr_q              (u_aes_core.u_aes_prng_clearing.u_lfsr.lfsr_q),
    .seed_en             (u_aes_core.u_aes_prng_clearing.seed_en),

    .key_touch_forces_reseed(u_aes_core.key_touch_forces_reseed),
    .key_init_new_pulse     (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                             u_aes_control_fsm.key_init_new_pulse),
    .alert_fatal            (u_aes_core.alert_fatal_o),

    .entropy_masking_req (entropy_masking_req),
    .entropy_masking_ack (entropy_masking_ack)
  );

if (`EN_MASKING) begin : gen_prng_bind
  bind aes aes_masking_reseed_if u_aes_masking_reseed_if (
    .clk_i,
    .rst_ni,

    .entropy_masking_req(entropy_masking_req),

    .entropy_i(edn_data),
    .lfsr_q_0 (u_aes_core.u_aes_cipher_core.gen_masks.u_aes_prng_masking.gen_lfsrs[0].u_lfsr_chunk.
               lfsr_q),
    .lfsr_q_1 (u_aes_core.u_aes_cipher_core.gen_masks.u_aes_prng_masking.gen_lfsrs[1].u_lfsr_chunk.
               lfsr_q),
    .lfsr_q_2 (u_aes_core.u_aes_cipher_core.gen_masks.u_aes_prng_masking.gen_lfsrs[2].u_lfsr_chunk.
               lfsr_q),
    .lfsr_q_3 (u_aes_core.u_aes_cipher_core.gen_masks.u_aes_prng_masking.gen_lfsrs[3].u_lfsr_chunk.
               lfsr_q),
    .lfsr_q_4 (u_aes_core.u_aes_cipher_core.gen_masks.u_aes_prng_masking.gen_lfsrs[4].u_lfsr_chunk.
               lfsr_q),

    .reseed_rate    (u_aes_core.prng_reseed_rate_q),
    .block_ctr_expr (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                     u_aes_control_fsm.block_ctr_expr),
    .ctrl_state     (u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                     u_aes_control_fsm.aes_ctrl_cs),
    .ctrl_state_next(u_aes_core.u_aes_control.gen_fsm[0].gen_fsm_p.u_aes_control_fsm_i.
                     u_aes_control_fsm.aes_ctrl_ns),
    .alert_fatal    (u_aes_core.alert_fatal_o),
    .seed_en        (u_aes_core.u_aes_cipher_core.gen_masks.u_aes_prng_masking.prng_seed_en)
  );
end
endmodule
