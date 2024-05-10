// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// Clock manager coverage bindings for multi bus input
module clkmgr_cov_bind;
% for i in range(len(hint_names)):
  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_idle_${i}_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (idle_i[${i}])
  );
% endfor

  bind clkmgr cip_lc_tx_cov_if u_lc_hw_debug_en_mubi_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_hw_debug_en_i)
  );

  bind clkmgr cip_lc_tx_cov_if u_lc_clk_byp_req_mubi_cov_if (
    .rst_ni (rst_ni),
    .val    (lc_clk_byp_req_i)
  );

  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_io_clk_byp_ack_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (io_clk_byp_ack_i)
  );

  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_all_clk_byp_ack_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (all_clk_byp_ack_i)
  );

  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_div_step_down_req_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (div_step_down_req_i)
  );

endmodule // clkmgr_cov_bind
