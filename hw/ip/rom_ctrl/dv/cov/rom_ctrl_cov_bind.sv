// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds functional coverage interaface to the top level rom_ctrl module.
module rom_ctrl_cov_bind;

  bind rom_ctrl rom_ctrl_cov_if u_rom_ctrl_cov_if (.*);

endmodule
