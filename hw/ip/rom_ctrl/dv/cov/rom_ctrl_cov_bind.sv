// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds functional coverage interaface to the top level rom_ctrl module.
module rom_ctrl_cov_bind;

  bind rom_ctrl rom_ctrl_cov_if u_rom_ctrl_cov_if (.*);

  bind tb.dut.gen_fsm_scramble_enabled.u_checker_fsm cip_mubi_cov_if #(.Width(4))
  u_rom_select_bus_o_cov_if (
    .rst_ni (rst_ni),
    .mubi   (rom_select_bus_o)
  );

endmodule
