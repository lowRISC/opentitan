// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_esc_rxtx_bind_fpv;

  bind prim_esc_rxtx_fpv
        prim_esc_rxtx_assert_fpv prim_esc_rxtx_assert_fpv (
    .clk_i       ,
    .rst_ni      ,
    .resp_err_pi ,
    .resp_err_ni ,
    .esc_err_pi  ,
    .esc_err_ni  ,
    .esc_req_i   ,
    .ping_req_i  ,
    .ping_ok_o   ,
    .integ_fail_o,
    .esc_en_o
  );

endmodule : prim_esc_rxtx_bind_fpv
