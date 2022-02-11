// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds functional coverage interaface to the top level sram_ctrl module.
module sram_ctrl_cov_bind;

  bind sram_ctrl cip_mubi_cov_if #(.Width(4)) u_hw_debug_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_hw_debug_en_i)
  );

  bind sram_ctrl cip_mubi_cov_if #(.Width(8)) u_otp_en_sram_ifetch_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (otp_en_sram_ifetch_i)
  );

endmodule
