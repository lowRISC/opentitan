// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds SYSRST_CTRL functional coverage interface to the top level SYSRST_CTRL module.
module sysrst_ctrl_cov_bind;
  bind sysrst_ctrl sysrst_ctrl_cov_if u_sysrst_ctrl_cov_if (.*);
endmodule

