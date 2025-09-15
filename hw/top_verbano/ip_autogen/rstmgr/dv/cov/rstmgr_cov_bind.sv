// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// Reset manager coverage bindings for multi bus input
module rstmgr_cov_bind;
  // sec cm coverage bind
  bind rstmgr cip_mubi_cov_if #(.Width(prim_mubi_pkg::MuBi4Width)) u_scanmode_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (scanmode_i)
  );
endmodule
