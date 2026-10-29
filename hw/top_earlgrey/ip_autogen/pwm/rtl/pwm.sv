// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module pwm
  import pwm_reg_pkg::NumAlerts;
  import pwm_reg_pkg::pwm_num_regs;
#(
  parameter int unsigned                    NOutputs                  = 6,
  parameter logic [NumAlerts-1:0]           AlertAsyncOn              = {NumAlerts{1'b1}},
  // Number of cycles a differential skew is tolerated on the alert signal
  parameter int unsigned                    AlertSkewCycles           = 1,
  parameter bit                             EnableRacl                = 1'b0,
  parameter bit                             RaclErrorRsp              = EnableRacl,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelVec[pwm_num_regs(NOutputs)] =
                                              '{pwm_num_regs(NOutputs){0}},
  parameter int                             PhaseCntDw                = 16,
  parameter int                             BeatCntDw                 = 27
) (
  input                       clk_i,
  input                       rst_ni,

  input                       clk_core_i,
  input                       rst_core_ni,

  input                       tlul_pkg::tl_h2d_t tl_i,
  output                      tlul_pkg::tl_d2h_t tl_o,

  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t  racl_policies_i,
  output top_racl_pkg::racl_error_log_t   racl_error_o,

  output logic [NOutputs-1:0] cio_pwm_o,
  output logic [NOutputs-1:0] cio_pwm_en_o
);

  pwm_reg_pkg::pwm_reg2hw_alert_test_reg_t                  reg2hw_alert_test;
  pwm_reg_pkg::pwm_reg2hw_cfg_reg_t                         reg2hw_cfg;
  pwm_reg_pkg::pwm_reg2hw_pwm_en_mreg_t      [NOutputs-1:0] reg2hw_pwm_en;
  pwm_reg_pkg::pwm_reg2hw_invert_mreg_t      [NOutputs-1:0] reg2hw_invert;
  pwm_reg_pkg::pwm_reg2hw_pwm_param_mreg_t   [NOutputs-1:0] reg2hw_pwm_param;
  pwm_reg_pkg::pwm_reg2hw_duty_cycle_mreg_t  [NOutputs-1:0] reg2hw_duty_cycle;
  pwm_reg_pkg::pwm_reg2hw_blink_param_mreg_t [NOutputs-1:0] reg2hw_blink_param;
  logic [NumAlerts-1:0] alert_test, alerts;

  pwm_reg_top #(
    .NOutputs(NOutputs),
    .EnableRacl(EnableRacl),
    .RaclErrorRsp(RaclErrorRsp),
    .RaclPolicySelVec(RaclPolicySelVec)
  ) u_reg (
    .clk_i,
    .rst_ni,
    .clk_core_i,
    .rst_core_ni,
    .tl_i             (tl_i),
    .tl_o             (tl_o),
    .reg2hw_alert_test_o  (reg2hw_alert_test),
    .reg2hw_cfg_o         (reg2hw_cfg),
    .reg2hw_pwm_en_o      (reg2hw_pwm_en),
    .reg2hw_invert_o      (reg2hw_invert),
    .reg2hw_pwm_param_o   (reg2hw_pwm_param),
    .reg2hw_duty_cycle_o  (reg2hw_duty_cycle),
    .reg2hw_blink_param_o (reg2hw_blink_param),
    .racl_policies_i  (racl_policies_i),
    .racl_error_o     (racl_error_o),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o       (alerts[0])
  );

  assign alert_test = {
    reg2hw_alert_test.q &
    reg2hw_alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
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

  assign cio_pwm_en_o = {NOutputs{1'b1}};

  pwm_core #(
    .NOutputs(NOutputs),
    .PhaseCntDw(PhaseCntDw),
    .BeatCntDw(BeatCntDw)
  ) u_pwm_core (
    .clk_core_i,
    .rst_core_ni,
    .cfg_i         (reg2hw_cfg),
    .pwm_en_i      (reg2hw_pwm_en),
    .invert_i      (reg2hw_invert),
    .pwm_param_i   (reg2hw_pwm_param),
    .duty_cycle_i  (reg2hw_duty_cycle),
    .blink_param_i (reg2hw_blink_param),
    .pwm_o         (cio_pwm_o)
  );

  `OCAH_OT_ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `OCAH_OT_ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  `OCAH_OT_ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)

  `OCAH_OT_ASSERT_KNOWN(CioPWMKnownO_A, cio_pwm_o)
  `OCAH_OT_ASSERT(CioPWMEnIsOneO_A, (&cio_pwm_en_o) === 1'b1)

  `OCAH_OT_ASSERT_KNOWN(RaclErrorValidKnown_A, racl_error_o.valid)

  // Alert assertions for reg_we onehot check
  `OCAH_OT_ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule : pwm
