// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: sysrst_ctrl key-triggered interrupt Module
//
module sysrst_ctrl_keyintr
  import sysrst_ctrl_reg_pkg::*;
(
  input                                                 clk_i,
  input                                                 rst_ni,
  // (Optionally) inverted input signals on AON clock
  input                                                 pwrb_int_i,
  input                                                 key0_int_i,
  input                                                 key1_int_i,
  input                                                 key2_int_i,
  input                                                 ac_present_int_i,
  input                                                 ec_rst_l_int_i,
  // CSRs synced to AON clock
  input  sysrst_ctrl_reg2hw_key_intr_ctl_reg_t          key_intr_ctl_i,
  input  sysrst_ctrl_reg2hw_key_intr_debounce_ctl_reg_t key_intr_debounce_ctl_i,
  output sysrst_ctrl_hw2reg_key_intr_status_reg_t       key_intr_status_o,
  // IRQ running on bus clock
  output                                                sysrst_ctrl_key_intr_o
);

  localparam int NumKeyIntr = 6;
  logic [NumKeyIntr-1:0] triggers, l2h_en, h2l_en;
  assign triggers = {
    pwrb_int_i, key0_int_i, key1_int_i, key2_int_i, ac_present_int_i, ec_rst_l_int_i
  };
  assign l2h_en = {
    key_intr_ctl_i.pwrb_in_l2h.q,
    key_intr_ctl_i.key0_in_l2h.q,
    key_intr_ctl_i.key1_in_l2h.q,
    key_intr_ctl_i.key2_in_l2h.q,
    key_intr_ctl_i.ac_present_l2h.q,
    key_intr_ctl_i.ec_rst_l_l2h.q
  };
  assign h2l_en = {
    key_intr_ctl_i.pwrb_in_h2l.q,
    key_intr_ctl_i.key0_in_h2l.q,
    key_intr_ctl_i.key1_in_h2l.q,
    key_intr_ctl_i.key2_in_h2l.q,
    key_intr_ctl_i.ac_present_h2l.q,
    key_intr_ctl_i.ec_rst_l_h2l.q
  };

  logic [NumKeyIntr-1:0] l2h_met_pulse, h2l_met_pulse;
  for (genvar k = 0; k < NumKeyIntr; k++) begin : gen_keyfsm
    // Instantiate the key state machine
    logic l2h_met_d, h2l_met_d;
    sysrst_ctrl_keyfsm #(
      .TimerWidth(TimerWidth)
    ) u_pwrbintr_fsm (
      .clk_i,
      .rst_ni,
      .trigger_i(triggers[k]),
      .cfg_timer_i(key_intr_debounce_ctl_i.q),
      .cfg_l2h_en_i(l2h_en[k]),
      .cfg_h2l_en_i(h2l_en[k]),
      .timer_l2h_cond_met_o(l2h_met_d),
      .timer_h2l_cond_met_o(h2l_met_d)
    );

    // generate a pulses for interrupt status CSR
    logic l2h_met_q, h2l_met_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin : p_pulse_reg
      if (!rst_ni) begin
        l2h_met_q <= '0;
        h2l_met_q <= '0;
      end else begin
        l2h_met_q <= l2h_met_d;
        h2l_met_q <= h2l_met_d;
      end
    end

    assign l2h_met_pulse[k] = l2h_met_d & ~l2h_met_q;
    assign h2l_met_pulse[k] = h2l_met_d & ~h2l_met_q;
  end

  // Assign to CSRs
  assign {key_intr_status_o.pwrb_l2h.de,
          key_intr_status_o.key0_in_l2h.de,
          key_intr_status_o.key1_in_l2h.de,
          key_intr_status_o.key2_in_l2h.de,
          key_intr_status_o.ac_present_l2h.de,
          key_intr_status_o.ec_rst_l_l2h.de} = l2h_met_pulse;

  assign {key_intr_status_o.pwrb_h2l.de,
          key_intr_status_o.key0_in_h2l.de,
          key_intr_status_o.key1_in_h2l.de,
          key_intr_status_o.key2_in_h2l.de,
          key_intr_status_o.ac_present_h2l.de,
          key_intr_status_o.ec_rst_l_h2l.de} = h2l_met_pulse;

  // Send out aggregated interrupt pulse
  assign sysrst_ctrl_key_intr_o = |l2h_met_pulse | |h2l_met_pulse;

  // To write into interrupt status register
  assign key_intr_status_o.pwrb_h2l.d = 1'b1;
  assign key_intr_status_o.pwrb_l2h.d = 1'b1;
  assign key_intr_status_o.key0_in_h2l.d = 1'b1;
  assign key_intr_status_o.key0_in_l2h.d = 1'b1;
  assign key_intr_status_o.key1_in_h2l.d = 1'b1;
  assign key_intr_status_o.key1_in_l2h.d = 1'b1;
  assign key_intr_status_o.key2_in_h2l.d = 1'b1;
  assign key_intr_status_o.key2_in_l2h.d = 1'b1;
  assign key_intr_status_o.ac_present_h2l.d = 1'b1;
  assign key_intr_status_o.ac_present_l2h.d = 1'b1;
  assign key_intr_status_o.ec_rst_l_h2l.d = 1'b1;
  assign key_intr_status_o.ec_rst_l_l2h.d = 1'b1;

endmodule
