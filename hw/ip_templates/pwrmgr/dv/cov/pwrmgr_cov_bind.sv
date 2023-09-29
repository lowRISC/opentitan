// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// Power manager coverage bindings for multi bus input
module pwrmgr_cov_bind;

  bind pwrmgr cip_lc_tx_cov_if u_lc_dft_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .val   (lc_dft_en_i)
  );

  bind pwrmgr cip_lc_tx_cov_if u_lc_hw_debug_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .val   (lc_hw_debug_en_i)
  );

  bind pwrmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_rom_ctrl_good_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (rom_ctrl_i.done)
  );

  bind pwrmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_rom_ctrl_done_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (rom_ctrl_i.good)
  );

  bind pwrmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_sw_rst_req_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (sw_rst_req_i)
  );
endmodule // pwrmgr_cov_bind
