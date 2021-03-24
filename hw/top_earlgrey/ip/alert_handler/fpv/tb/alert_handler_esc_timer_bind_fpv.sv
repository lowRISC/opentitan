// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module alert_handler_esc_timer_bind_fpv;


  bind alert_handler_esc_timer
      alert_handler_esc_timer_assert_fpv i_alert_handler_esc_timer_assert_fpv (
    .clk_i,
    .rst_ni,
    .en_i,
    .clr_i,
    .accum_trig_i,
    .timeout_en_i,
    .timeout_cyc_i,
    .esc_en_i,
    .esc_map_i,
    .phase_cyc_i,
    .esc_trig_o,
    .esc_cnt_o,
    .esc_sig_en_o,
    .esc_state_o
  );


endmodule : alert_handler_esc_timer_bind_fpv
