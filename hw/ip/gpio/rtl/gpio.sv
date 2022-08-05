// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// General Purpose Input/Output module

`include "prim_assert.sv"

module gpio
  import gpio_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // This parameter instantiates 2-stage synchronizers on all GPIO inputs.
  parameter bit GpioAsyncOn = 1
) (
  input clk_i,
  input rst_ni,

  // Bus interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupts
  output logic [31:0] intr_gpio_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // GPIOs
  input        [31:0] cio_gpio_i,
  output logic [31:0] cio_gpio_o,
  output logic [31:0] cio_gpio_en_o
);



  gpio_reg2hw_t reg2hw;
  gpio_hw2reg_t hw2reg;

  logic [31:0] cio_gpio_q;
  logic [31:0] cio_gpio_en_q;

  // possibly filter the input based upon register configuration
  logic [31:0] data_in_d;
  localparam int unsigned CntWidth = 4;
  for (genvar i = 0 ; i < 32 ; i++) begin : gen_filter
    prim_filter_ctr #(
      .AsyncOn(GpioAsyncOn),
      .CntWidth(CntWidth)
    ) u_filter (
      .clk_i,
      .rst_ni,
      .enable_i(reg2hw.ctrl_en_input_filter.q[i]),
      .filter_i(cio_gpio_i[i]),
      .thresh_i({CntWidth{1'b1}}),
      .filter_o(data_in_d[i])
    );
  end

  // GPIO_IN
  assign hw2reg.data_in.de = 1'b1;
  assign hw2reg.data_in.d  = data_in_d;

  // GPIO_OUT
  assign cio_gpio_o                     = cio_gpio_q;
  assign cio_gpio_en_o                  = cio_gpio_en_q;

  assign hw2reg.direct_out.d            = cio_gpio_q;
  assign hw2reg.masked_out_upper.data.d = cio_gpio_q[31:16];
  assign hw2reg.masked_out_upper.mask.d = 16'h 0;
  assign hw2reg.masked_out_lower.data.d = cio_gpio_q[15:0];
  assign hw2reg.masked_out_lower.mask.d = 16'h 0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cio_gpio_q  <= '0;
    end else if (reg2hw.direct_out.qe) begin
      cio_gpio_q <= reg2hw.direct_out.q;
    end else if (reg2hw.masked_out_upper.data.qe) begin
      cio_gpio_q[31:16] <=
        ( reg2hw.masked_out_upper.mask.q & reg2hw.masked_out_upper.data.q) |
        (~reg2hw.masked_out_upper.mask.q & cio_gpio_q[31:16]);
    end else if (reg2hw.masked_out_lower.data.qe) begin
      cio_gpio_q[15:0] <=
        ( reg2hw.masked_out_lower.mask.q & reg2hw.masked_out_lower.data.q) |
        (~reg2hw.masked_out_lower.mask.q & cio_gpio_q[15:0]);
    end
  end

  // GPIO OE
  assign hw2reg.direct_oe.d = cio_gpio_en_q;
  assign hw2reg.masked_oe_upper.data.d = cio_gpio_en_q[31:16];
  assign hw2reg.masked_oe_upper.mask.d = 16'h 0;
  assign hw2reg.masked_oe_lower.data.d = cio_gpio_en_q[15:0];
  assign hw2reg.masked_oe_lower.mask.d = 16'h 0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cio_gpio_en_q  <= '0;
    end else if (reg2hw.direct_oe.qe) begin
      cio_gpio_en_q <= reg2hw.direct_oe.q;
    end else if (reg2hw.masked_oe_upper.data.qe) begin
      cio_gpio_en_q[31:16] <=
        ( reg2hw.masked_oe_upper.mask.q & reg2hw.masked_oe_upper.data.q) |
        (~reg2hw.masked_oe_upper.mask.q & cio_gpio_en_q[31:16]);
    end else if (reg2hw.masked_oe_lower.data.qe) begin
      cio_gpio_en_q[15:0] <=
        ( reg2hw.masked_oe_lower.mask.q & reg2hw.masked_oe_lower.data.q) |
        (~reg2hw.masked_oe_lower.mask.q & cio_gpio_en_q[15:0]);
    end
  end

  logic [31:0] data_in_q;
  always_ff @(posedge clk_i) begin
    data_in_q <= data_in_d;
  end

  logic [31:0] event_intr_rise, event_intr_fall, event_intr_actlow, event_intr_acthigh;
  logic [31:0] event_intr_combined;

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(32)) intr_hw (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_intr_combined),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.d),
    .intr_o                 (intr_gpio_o)
  );

  // detect four possible individual interrupts
  assign event_intr_rise    = (~data_in_q &  data_in_d) & reg2hw.intr_ctrl_en_rising.q;
  assign event_intr_fall    = ( data_in_q & ~data_in_d) & reg2hw.intr_ctrl_en_falling.q;
  assign event_intr_acthigh =                data_in_d  & reg2hw.intr_ctrl_en_lvlhigh.q;
  assign event_intr_actlow  =               ~data_in_d  & reg2hw.intr_ctrl_en_lvllow.q;

  assign event_intr_combined = event_intr_rise   |
                               event_intr_fall   |
                               event_intr_actlow |
                               event_intr_acthigh;

  // Alerts
  logic [NumAlerts-1:0] alert_test, alerts;
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Register module
  gpio_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .reg2hw,
    .hw2reg,

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0]),
    .devmode_i  (1'b1)
  );

  // Assert Known: Outputs
  `ASSERT_KNOWN(IntrGpioKnown, intr_gpio_o)
  `ASSERT_KNOWN(CioGpioEnOKnown, cio_gpio_en_o)
  `ASSERT_KNOWN(CioGpioOKnown, cio_gpio_o)
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
