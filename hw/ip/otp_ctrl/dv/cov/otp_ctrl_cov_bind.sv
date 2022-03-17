// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds OTP_CTRL functional coverage interaface to the top level OTP_CTRL module.
module otp_ctrl_cov_bind;

  bind otp_ctrl otp_ctrl_cov_if u_otp_ctrl_cov_if (
    .pwr_otp_o        (pwr_otp_o),
    .lc_otp_program_i (lc_otp_program_i),
    .lc_escalate_en_i (lc_escalate_en_i),
    .flash_otp_key_i  (flash_otp_key_i),
    .sram_otp_key_i   (sram_otp_key_i),
    .otbn_otp_key_i   (otbn_otp_key_i)
  );

  bind otp_ctrl cip_mubi_cov_if #(.Width(4)) u_lc_creator_seed_sw_rw_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_creator_seed_sw_rw_en_i)
  );

  bind otp_ctrl cip_mubi_cov_if #(.Width(4)) u_lc_seed_hw_rd_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_seed_hw_rd_en_i)
  );

  bind otp_ctrl cip_mubi_cov_if #(.Width(4)) u_lc_dft_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_dft_en_i)
  );

  bind otp_ctrl cip_mubi_cov_if #(.Width(4)) u_lc_escalate_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_escalate_en_i)
  );

  bind otp_ctrl cip_mubi_cov_if #(.Width(4)) u_lc_check_byp_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_check_byp_en_i)
  );
endmodule
