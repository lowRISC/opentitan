// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds AES functional coverage interaface to the top level AES module.
module aes_cov_bind;

  bind aes aes_cov_if u_aes_cov_if (
    .clk_i  (clk_i),
    .idle_i (idle_o == prim_mubi_pkg::MuBi4True)
  );

  bind aes  cip_lc_tx_cov_if u_lc_escalate_en_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_escalate_en_i)
  );
endmodule
