// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds LC_CTRL functional coverage interaface to the top level LC_CTRL module.
module lc_ctrl_cov_bind;
  // LC_CTRL FSM coverage
  bind lc_ctrl_fsm lc_ctrl_fsm_cov_if u_lc_ctrl_fsm_cov_if (.*);

  // MUBI coverage
  bind lc_ctrl cip_mubi_cov_if #(
    .Width(4)
  ) u_scanmode_i_if (
    .rst_ni(rst_ni),
    .mubi  (scanmode_i)
  );
  bind lc_ctrl cip_lc_tx_cov_if u_lc_clk_byp_ack_i_if (
    .rst_ni(rst_ni),
    .val(lc_clk_byp_ack_i)
  );
  bind lc_ctrl cip_lc_tx_cov_if u_lc_flash_rma_ack_i_if (
    .rst_ni(rst_ni),
    .val(lc_flash_rma_ack_i)
  );
  // otp_lc_data_t otp_lc_data_i struct
  bind lc_ctrl cip_lc_tx_cov_if u_otp_lc_data_i_secrets_valid_if (
    .rst_ni(rst_ni),
    .val(otp_lc_data_i.secrets_valid)
  );
  bind lc_ctrl cip_lc_tx_cov_if u_otp_lc_data_i_test_tokens_valid_if (
    .rst_ni(rst_ni),
    .val(otp_lc_data_i.test_tokens_valid)
  );
  bind lc_ctrl cip_lc_tx_cov_if u_otp_lc_data_i_rma_token_valid_if (
    .rst_ni(rst_ni),
    .val(otp_lc_data_i.rma_token_valid)
  );

endmodule
