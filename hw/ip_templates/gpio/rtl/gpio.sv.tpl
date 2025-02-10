// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// General Purpose Input/Output module

`include "prim_assert.sv"

module ${module_instance_name}
  import ${module_instance_name}_pkg::*;
  import ${module_instance_name}_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0]           AlertAsyncOn              = {NumAlerts{1'b1}},
  parameter bit                             GpioAsHwStrapsEn          = 1,
  // This parameter instantiates 2-stage synchronizers on all GPIO inputs.
  parameter bit                             GpioAsyncOn               = 1,
  parameter bit                             EnableRacl                = 1'b0,
  parameter bit                             RaclErrorRsp              = 1'b1,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelVec[NumRegs] = '{NumRegs{0}}
) (
  input clk_i,
  input rst_ni,

  // Strap sampling trigger and broadcast output
  input strap_en_i,
  output gpio_straps_t sampled_straps_o,

  // Bus interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupts
  output logic [NumIOs-1:0] intr_gpio_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t  racl_policies_i,
  output top_racl_pkg::racl_error_log_t   racl_error_o,

  // GPIOs
  input        [NumIOs-1:0] cio_gpio_i,
  output logic [NumIOs-1:0] cio_gpio_o,
  output logic [NumIOs-1:0] cio_gpio_en_o
);
% if num_inp_period_counters > 0:
  localparam int unsigned IOWidth = prim_util_pkg::vbits(NumIOs);

% endif
  ${module_instance_name}_reg2hw_t reg2hw;
  ${module_instance_name}_hw2reg_t hw2reg;

  logic [NumIOs-1:0] cio_gpio_q;
  logic [NumIOs-1:0] cio_gpio_en_q;

  // possibly filter the input based upon register configuration
  logic [NumIOs-1:0] data_in_d;
  localparam int unsigned CntWidth = 4;
  for (genvar i = 0 ; i < NumIOs ; i++) begin : gen_filter
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

  // Detect rising and falling edges.
  logic [NumIOs-1:0] data_in_q, event_rise, event_fall;
  always_ff @(posedge clk_i) begin
    data_in_q <= data_in_d;
  end
  assign event_rise = data_in_d & ~data_in_q;
  assign event_fall = ~data_in_d & data_in_q;

% if num_inp_period_counters > 0:
  // Input period counters
  logic [NumInpPeriodCounters-1:0] inp_prd_cnt_clr, inp_prd_cnt_inc;
  logic [NumInpPeriodCounters-1:0][31:0] inp_prd_cnt_d, inp_prd_cnt_q;
  logic [NumInpPeriodCounters-1:0][7:0] prescaler_cnt_d, prescaler_cnt_q;
  logic [NumInpPeriodCounters-1:0] prescaler_cnt_reached, relevant_edge, relevant_edge_clr;
  logic [NumInpPeriodCounters-1:0] relevant_edge_d, relevant_edge_q;
  typedef enum logic [1:0] {
    InpPrdCntDisabled,
    InpPrdCntPreOpeningEdge,
    InpPrdCntPreClosingEdge
  } inp_prd_cnt_state_e;
  inp_prd_cnt_state_e [NumInpPeriodCounters-1:0] inp_prd_cnt_state_d, inp_prd_cnt_state_q;

  logic [NumInpPeriodCounters-1:0] unused_input_select;
  for (genvar i = 0; i < NumInpPeriodCounters; i++) begin : gen_inp_prd_cnt

    // Determine when the prescaler counter reaches the prescaler threshold.
    assign prescaler_cnt_reached[i] =
        (prescaler_cnt_q[i] == reg2hw.inp_prd_cnt_ctrl[i].prescaler.q) &
        reg2hw.inp_prd_cnt_ctrl[i].enable.q;

    always_comb begin
      prescaler_cnt_d[i] = prescaler_cnt_q[i];

      if (!reg2hw.inp_prd_cnt_ctrl[i].enable.q) begin
        // Clear the prescaler counter when the input period counter is disabled.
        prescaler_cnt_d[i] = '0;
      end else begin
        // When the input period counter is enabled ..
        if (prescaler_cnt_reached[i]) begin
          // .. and the prescaler counter has reached its threshold, clear it, ..
          prescaler_cnt_d[i] = '0;
        end else begin
          // .. otherwise increment it.
          prescaler_cnt_d[i] = prescaler_cnt_q[i] + 8'd1;
        end
      end
    end

    // Detect relevant edges.
    assign relevant_edge[i] = reg2hw.inp_prd_cnt_ctrl[i].polarity.q ?
                              // Rising edge
                              event_rise[reg2hw.inp_prd_cnt_ctrl[i].input_select.q[IOWidth-1:0]] :
                              // Falling edge
                              event_fall[reg2hw.inp_prd_cnt_ctrl[i].input_select.q[IOWidth-1:0]];

    assign unused_input_select[i] = ^reg2hw.inp_prd_cnt_ctrl[i].input_select.q[7:IOWidth];

    // Flop relevant edges until the prescaler counter reaches its threshold.
    always_comb begin
      // Hold by default
      relevant_edge_d[i] = relevant_edge_q[i];

      // Detected relevant edges take precedence.
      if (relevant_edge[i]) begin
        relevant_edge_d[i] = 1'b1;
      end else if (relevant_edge_clr[i]) begin
        // Clear flopped relevant edge when it was consumed by the FSM.
        relevant_edge_d[i] = 1'b0;
      end
    end

    // Combinational logic of input period counter.
    always_comb begin
      // Hold by default
      inp_prd_cnt_d[i] = inp_prd_cnt_q[i];

      // Clearing takes precendence
      if (inp_prd_cnt_clr[i]) begin
        inp_prd_cnt_d[i] = '0;
      end else if (inp_prd_cnt_inc[i] && inp_prd_cnt_q[i] != '1) begin
        // Increment if the counter hasn't reached its maximum value yet.
        inp_prd_cnt_d[i] = inp_prd_cnt_q[i] + 32'd1;
      end
    end

    // Simple FSM controlling the input period counter.
    always_comb begin
      hw2reg.inp_prd_cnt_ctrl[i].enable.de = 1'b0;
      hw2reg.inp_prd_cnt_val[i].de = 1'b0;
      inp_prd_cnt_clr[i] = 1'b0;
      inp_prd_cnt_inc[i] = 1'b0;
      inp_prd_cnt_state_d[i] = inp_prd_cnt_state_q[i];
      relevant_edge_clr[i] = 1'b0;

      unique case (inp_prd_cnt_state_q[i])
        InpPrdCntDisabled: begin
          if (reg2hw.inp_prd_cnt_ctrl[i].enable.q) begin
            // When the input period counter gets enabled, clear the counter and wait for the
            // opening edge.
            inp_prd_cnt_clr[i] = 1'b1;
            inp_prd_cnt_state_d[i] = InpPrdCntPreOpeningEdge;
          end
        end

        InpPrdCntPreOpeningEdge: begin
          // Wait for the opening edge.
          if (relevant_edge_q[i]) begin
            // Clear the relevant edge and switch to waiting for the closing edge.
            relevant_edge_clr[i] = 1'b1;
            inp_prd_cnt_state_d[i] = InpPrdCntPreClosingEdge;
          end
        end

        InpPrdCntPreClosingEdge: begin
          if (prescaler_cnt_reached[i]) begin
            // Increment the counter while waiting for the closing edge.
            inp_prd_cnt_inc[i] = 1'b1;
            if (relevant_edge_q[i]) begin
              // Clear the relevant edge.
              relevant_edge_clr[i] = 1'b1;
              // Update the value register of this input period counter.
              hw2reg.inp_prd_cnt_val[i].de = 1'b1;
              // Clear the counter.
              inp_prd_cnt_clr[i] = 1'b1;
              // If continuous mode is not enabled, clear the enable bit and go back to the disabled
              // state.
              if (!reg2hw.inp_prd_cnt_ctrl[i].continuous_mode.q) begin
                hw2reg.inp_prd_cnt_ctrl[i].enable.de = 1'b1;
                inp_prd_cnt_state_d[i] = InpPrdCntDisabled;
              end
              // Else, (i.e., if continuous mode is enabled), implicitly don't clear the enable bit
              // and keep waiting for the next closing edge.
            end
          end
        end

        default: inp_prd_cnt_state_d[i] = InpPrdCntDisabled;
      endcase

      // When the input period counter is not enabled, clear the counter and the relevant edge flop,
      // and go back to the disabled state.
      if (!reg2hw.inp_prd_cnt_ctrl[i].enable.q) begin
        inp_prd_cnt_clr[i] = 1'b1;
        relevant_edge_clr[i] = 1'b1;
        inp_prd_cnt_state_d[i] = InpPrdCntDisabled;
      end
    end

    // When the SW-visible register gets updated, write the counter value (with saturation).
    assign hw2reg.inp_prd_cnt_val[i].d = inp_prd_cnt_q[i];

    // HW only ever clears the enable bit in the enable bit of the control register (in the FSM
    // above), it never writes any of the other bits.
    assign hw2reg.inp_prd_cnt_ctrl[i].enable.d = 1'b0;
    assign hw2reg.inp_prd_cnt_ctrl[i].continuous_mode.d = 1'b0;
    assign hw2reg.inp_prd_cnt_ctrl[i].continuous_mode.de = 1'b0;
    assign hw2reg.inp_prd_cnt_ctrl[i].polarity.d = 1'b0;
    assign hw2reg.inp_prd_cnt_ctrl[i].polarity.de = 1'b0;
    assign hw2reg.inp_prd_cnt_ctrl[i].input_select.d = '0;
    assign hw2reg.inp_prd_cnt_ctrl[i].input_select.de = 1'b0;
    assign hw2reg.inp_prd_cnt_ctrl[i].prescaler.d = '0;
    assign hw2reg.inp_prd_cnt_ctrl[i].prescaler.de = 1'b0;

    // Flops for each input period counter.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        inp_prd_cnt_q[i] <= '0;
        inp_prd_cnt_state_q[i] <= InpPrdCntDisabled;
        prescaler_cnt_q[i] <= '0;
        relevant_edge_q[i] <= 1'b0;
      end else begin
        inp_prd_cnt_q[i] <= inp_prd_cnt_d[i];
        inp_prd_cnt_state_q[i] <= inp_prd_cnt_state_d[i];
        prescaler_cnt_q[i] <= prescaler_cnt_d[i];
        relevant_edge_q[i] <= relevant_edge_d[i];
      end
    end
  end

% endif
  if (GpioAsHwStrapsEn) begin : gen_strap_sample
    // sample at gpio inputs at strap_en_i signal pulse.
    logic strap_en;

    // The strap_en_i is a single cycle pulse generated by the pwrmgr
    // Both sender (pwrmgr) and receiver (gpio controller) are in the same clock domain (io_div4)
    // A cdc synchronizer is not required
    //
    assign strap_en = strap_en_i;

    // we guarantee here by design that this will always be done exactly once per reset cycle.
    logic sample_trigger;
    assign sample_trigger                    = strap_en && !reg2hw.hw_straps_data_in_valid.q;
    assign hw2reg.hw_straps_data_in_valid.de = sample_trigger;
    assign hw2reg.hw_straps_data_in_valid.d  = 1'b1;
    assign hw2reg.hw_straps_data_in.de       = sample_trigger;
    assign hw2reg.hw_straps_data_in.d        = data_in_d;
    assign sampled_straps_o.data             = reg2hw.hw_straps_data_in.q;
    assign sampled_straps_o.valid            = reg2hw.hw_straps_data_in_valid.q;
  end else begin : gen_no_strap_sample
    assign hw2reg.hw_straps_data_in_valid.de = 1'b0;
    assign hw2reg.hw_straps_data_in_valid.d  = 1'b0;
    assign hw2reg.hw_straps_data_in.de       = 1'b0;
    assign hw2reg.hw_straps_data_in.d        = '0;
    assign sampled_straps_o.data             = '0;
    assign sampled_straps_o.valid            = 1'b0;

    logic unused_signals;
    assign unused_signals = ^{strap_en_i,
                              reg2hw.hw_straps_data_in.q,
                              reg2hw.hw_straps_data_in_valid.q};
  end

  // GPIO_IN
  assign hw2reg.data_in.de = 1'b1;
  assign hw2reg.data_in.d  = data_in_d;

  // GPIO_OUT
  assign cio_gpio_o                     = cio_gpio_q;
  assign cio_gpio_en_o                  = cio_gpio_en_q;

  assign hw2reg.direct_out.d            = cio_gpio_q;
  assign hw2reg.masked_out_upper.data.d = cio_gpio_q[NumIOs-1:16];
  assign hw2reg.masked_out_upper.mask.d = 16'h 0;
  assign hw2reg.masked_out_lower.data.d = cio_gpio_q[15:0];
  assign hw2reg.masked_out_lower.mask.d = 16'h 0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cio_gpio_q  <= '0;
    end else if (reg2hw.direct_out.qe) begin
      cio_gpio_q <= reg2hw.direct_out.q;
    end else if (reg2hw.masked_out_upper.data.qe) begin
      cio_gpio_q[NumIOs-1:16] <=
        ( reg2hw.masked_out_upper.mask.q & reg2hw.masked_out_upper.data.q) |
        (~reg2hw.masked_out_upper.mask.q & cio_gpio_q[NumIOs-1:16]);
    end else if (reg2hw.masked_out_lower.data.qe) begin
      cio_gpio_q[15:0] <=
        ( reg2hw.masked_out_lower.mask.q & reg2hw.masked_out_lower.data.q) |
        (~reg2hw.masked_out_lower.mask.q & cio_gpio_q[15:0]);
    end
  end

  // GPIO OE
  assign hw2reg.direct_oe.d = cio_gpio_en_q;
  assign hw2reg.masked_oe_upper.data.d = cio_gpio_en_q[NumIOs-1:16];
  assign hw2reg.masked_oe_upper.mask.d = 16'h 0;
  assign hw2reg.masked_oe_lower.data.d = cio_gpio_en_q[15:0];
  assign hw2reg.masked_oe_lower.mask.d = 16'h 0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cio_gpio_en_q  <= '0;
    end else if (reg2hw.direct_oe.qe) begin
      cio_gpio_en_q <= reg2hw.direct_oe.q;
    end else if (reg2hw.masked_oe_upper.data.qe) begin
      cio_gpio_en_q[NumIOs-1:16] <=
        ( reg2hw.masked_oe_upper.mask.q & reg2hw.masked_oe_upper.data.q) |
        (~reg2hw.masked_oe_upper.mask.q & cio_gpio_en_q[NumIOs-1:16]);
    end else if (reg2hw.masked_oe_lower.data.qe) begin
      cio_gpio_en_q[15:0] <=
        ( reg2hw.masked_oe_lower.mask.q & reg2hw.masked_oe_lower.data.q) |
        (~reg2hw.masked_oe_lower.mask.q & cio_gpio_en_q[15:0]);
    end
  end

  logic [NumIOs-1:0] event_intr_rise, event_intr_fall, event_intr_actlow, event_intr_acthigh;
  logic [NumIOs-1:0] event_intr_combined;

  // instantiate interrupt hardware primitive
  prim_intr_hw #(.Width(NumIOs)) intr_hw (
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
  assign event_intr_rise    = event_rise & reg2hw.intr_ctrl_en_rising.q;
  assign event_intr_fall    = event_fall & reg2hw.intr_ctrl_en_falling.q;
  assign event_intr_acthigh =  data_in_d & reg2hw.intr_ctrl_en_lvlhigh.q;
  assign event_intr_actlow  = ~data_in_d & reg2hw.intr_ctrl_en_lvllow.q;

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
  ${module_instance_name}_reg_top #(
    .EnableRacl(EnableRacl),
    .RaclErrorRsp(RaclErrorRsp),
    .RaclPolicySelVec(RaclPolicySelVec)
  ) u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .reg2hw,
    .hw2reg,

    .racl_policies_i,
    .racl_error_o,

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0])
  );

  // Assert Known: Outputs
  `ASSERT_KNOWN(IntrGpioKnown, intr_gpio_o)
  `ASSERT_KNOWN(CioGpioEnOKnown, cio_gpio_en_o)
  `ASSERT_KNOWN(CioGpioOKnown, cio_gpio_o)
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(RaclErrorValidKnown_A, racl_error_o.valid)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])

endmodule
