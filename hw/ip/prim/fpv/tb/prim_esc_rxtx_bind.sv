// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_esc_rxtx_bind;

  bind prim_esc_rxtx_tb prim_esc_rxtx_assert prim_esc_rxtx_assert (
    .clk_i       ,
    .rst_ni      ,
    .resp_err_pi ,
    .resp_err_ni ,
    .esc_err_pi  ,
    .esc_err_ni  ,
    .esc_en_i    ,
    .ping_en_i   ,
    .ping_ok_o   ,
    .integ_fail_o,
    .esc_en_o
  );

endmodule : prim_esc_rxtx_bind
