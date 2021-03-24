// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module alert_handler_ping_timer_bind_fpv;


  bind alert_handler_ping_timer
      alert_handler_ping_timer_assert_fpv i_alert_handler_ping_timer_assert_fpv (
    .clk_i,
    .rst_ni,
    .entropy_i,
    .en_i,
    .alert_en_i,
    .ping_timeout_cyc_i,
    .wait_cyc_mask_i,
    .alert_ping_en_o,
    .esc_ping_en_o,
    .alert_ping_ok_i,
    .esc_ping_ok_i,
    .alert_ping_fail_o,
    .esc_ping_fail_o
  );


endmodule : alert_handler_ping_timer_bind_fpv
