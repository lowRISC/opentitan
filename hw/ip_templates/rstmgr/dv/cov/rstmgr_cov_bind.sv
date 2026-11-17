// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// Reset manager coverage bindings for multi bus input
module rstmgr_cov_bind;
  // sec cm coverage bind
  // The scan mode enters the secondary partition only (scan_partition).

  bind rstmgr_part_secondary cip_mubi_cov_if #(
    .Width(prim_mubi_pkg::MuBi4Width)
  ) u_scanmode_mubi_cov_if (
    .rst_ni (rst_ni),
    .mubi   (scanmode_i)
  );
endmodule
