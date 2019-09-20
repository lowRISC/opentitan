// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module prim_alert_rxtx_bind;

  bind prim_alert_rxtx_tb prim_alert_rxtx_assert prim_alert_rxtx_assert (
    .clk_i,
    .rst_ni,
    .ping_err_pi,
    .ping_err_ni,
    .ack_err_pi,
    .ack_err_ni,
    .alert_err_pi,
    .alert_err_ni,
    .alert_i,
    .ping_en_i,
    .ping_ok_o,
    .integ_fail_o,
    .alert_o
  );

endmodule : prim_alert_rxtx_bind
