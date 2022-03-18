// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Add description here TBD
module pwrmgr_cov_bind;

  bind pwrmgr cip_mubi_cov_if #(.Width(lc_ctrl_pkg::TxWidth)) u_lc_dft_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_dft_en_i)
  );

  bind pwrmgr cip_mubi_cov_if #(.Width(lc_ctrl_pkg::TxWidth)) u_lc_hw_debug_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (lc_hw_debug_en_i)
  );

  bind pwrmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width*2)) u_rom_ctrl_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (rom_ctrl_i)
  );

  bind pwrmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_sw_rst_req_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (sw_rst_req_i)
  );
endmodule // pwrmgr_cov_bind
