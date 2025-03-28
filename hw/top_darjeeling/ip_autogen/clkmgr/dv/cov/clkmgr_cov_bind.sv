// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// Clock manager coverage bindings for multi bus input
module clkmgr_cov_bind;
  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_idle_0_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (idle_i[0])
  );
  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_idle_1_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (idle_i[1])
  );
  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_idle_2_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (idle_i[2])
  );
  bind clkmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_idle_3_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (idle_i[3])
  );

endmodule // clkmgr_cov_bind
