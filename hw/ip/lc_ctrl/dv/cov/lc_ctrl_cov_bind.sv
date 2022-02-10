// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds LC_CTRL functional coverage interaface to the top level LC_CTRL module.
module lc_ctrl_cov_bind;
  bind lc_ctrl_fsm lc_ctrl_fsm_cov_if u_lc_ctrl_fsm_cov_if (.*);
endmodule
