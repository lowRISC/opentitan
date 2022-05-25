// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl combo action Module
//
module sysrst_ctrl_comboact
  import sysrst_ctrl_reg_pkg::*;
(
  input clk_i,
  input rst_ni,

  input combo_det_pulse_i,
  input ec_rst_l_i,

  input cfg_bat_disable_en_i,
  input cfg_ec_rst_en_i,
  input cfg_rst_req_en_i,
  input cfg_intr_en_i,
  input sysrst_ctrl_reg2hw_ec_rst_ctl_reg_t ec_rst_ctl_i,

  output combo_intr_pulse_o,
  output bat_disable_o,
  output rst_req_o,
  output ec_rst_l_o
);

  ///////////////////////////////////////
  // Combo / EC reset detection Pulses //
  ///////////////////////////////////////

  // mask combo detection pulse with config bits
  logic combo_bat_disable_pulse, combo_ot_pulse, combo_ec_rst_pulse;
  assign combo_bat_disable_pulse = cfg_bat_disable_en_i & combo_det_pulse_i;
  assign combo_ec_rst_pulse      = cfg_ec_rst_en_i & combo_det_pulse_i;
  assign combo_ot_pulse         = cfg_rst_req_en_i & combo_det_pulse_i;
  assign combo_intr_pulse_o      = cfg_intr_en_i & combo_det_pulse_i;

  //ec_rst_l_i high->low detection
  logic ec_rst_l_det_pulse, ec_rst_l_det_q;
  assign ec_rst_l_det_pulse = ~ec_rst_l_i & ec_rst_l_det_q;

  ////////////////////////////////////
  // Bat / OT reset pulse latching //
  ////////////////////////////////////

  logic bat_disable_q, bat_disable_d;
  assign bat_disable_d = bat_disable_q | combo_bat_disable_pulse;
  assign bat_disable_o = bat_disable_q;

  logic rst_req_q, rst_req_d;
  assign rst_req_d = rst_req_q | combo_ot_pulse;
  assign rst_req_o = rst_req_q;

  ////////////////////
  // EC reset logic //
  ////////////////////

  // OT reset will also reset EC
  logic timer_expired;
  logic ec_rst_l_q, ec_rst_l_d;
  assign ec_rst_l_o = ec_rst_l_q;
  assign ec_rst_l_d = (combo_ec_rst_pulse ||
                       ec_rst_l_det_pulse) ? 1'b0 :
                      (timer_expired)      ? 1'b1 : ec_rst_l_q;


  // Reset stretching counter
  logic [TimerWidth-1:0] timer_cnt_d, timer_cnt_q;
  assign timer_expired = (ec_rst_l_q == 1'b0) && (timer_cnt_q == ec_rst_ctl_i.q);
  assign timer_cnt_d = (timer_expired)       ? '0                 :
                       (ec_rst_l_q == 1'b0)  ? timer_cnt_q + 1'b1 : timer_cnt_q;

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      bat_disable_q  <= 1'b0;
      ec_rst_l_det_q <= 1'b1;  // active low signal
      rst_req_q      <= 1'b0;
      ec_rst_l_q     <= 1'b0;  // asserted when power-on-reset is asserted
      timer_cnt_q    <= '0;
    end else begin
      bat_disable_q  <= bat_disable_d;
      ec_rst_l_det_q <= ec_rst_l_i;
      rst_req_q      <= rst_req_d;
      ec_rst_l_q     <= ec_rst_l_d;
      timer_cnt_q    <= timer_cnt_d;
    end
  end
endmodule
