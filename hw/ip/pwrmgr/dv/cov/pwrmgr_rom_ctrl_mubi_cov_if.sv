// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description:
// Adaptor to bind vector of rom_ctrl mubi fields

interface pwrmgr_rom_ctrl_mubi_cov_if #(
  parameter int Width = 8
) (
  input rom_ctrl_pkg::pwrmgr_data_t [Width-1:0] rom_ctrl_i,
  input logic rst_ni
);

  for (genvar k = 0; k < Width; k++) begin : gen_cov
    cip_mubi_cov_if #(
      .Width(prim_mubi_pkg::MuBi4Width)
    ) u_rom_ctrl_good_mubi_cov_if (
      .rst_ni(rst_ni),
      .mubi  (rom_ctrl_i[k].good)
    );

    cip_mubi_cov_if #(
      .Width(prim_mubi_pkg::MuBi4Width)
    ) u_rom_ctrl_done_mubi_cov_if (
      .rst_ni(rst_ni),
      .mubi  (rom_ctrl_i[k].done)
    );
  end
endinterface : pwrmgr_rom_ctrl_mubi_cov_if
