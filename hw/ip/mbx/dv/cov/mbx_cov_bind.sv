// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds MBX functional coverage interaface to the top level MBX module.
module mbx_cov_bind;
  // MBX _if coverage
  bind mbx mbx_cov_if u_mbx_cov_if (.clk(clk_i));
  bind mbx_hostif mbx_host_cov_if u_mbx_cov_hostif (.clk(clk_i), .reg2hw, .hw2reg);
  bind mbx_sysif mbx_sys_cov_if u_mbx_cov_sysif (.clk(clk_i), .reg2hw, .hw2reg);

  // MBX FSM coverage
  bind mbx_fsm mbx_fsm_cov_if u_mbx_fsm_cov_if (.*);

  //FIXME: Review, cip_lc_tx/cip_mubi

endmodule
