// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module ${module_instance_name}
  import ${module_instance_name}_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0]           AlertAsyncOn              = {NumAlerts{1'b1}},
  parameter bit                             EnableRacl                = 1'b0,
  parameter bit                             RaclErrorRsp              = EnableRacl,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelVec[NumRegs] = '{NumRegs{0}},
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

  ${module_instance_name}_reg_pkg::pwm_reg2hw_t reg2hw;
  logic [NumAlerts-1:0] alert_test, alerts;

  ${module_instance_name}_reg_top #(
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
    .reg2hw           (reg2hw),
    .racl_policies_i  (racl_policies_i),
    .racl_error_o     (racl_error_o),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o       (alerts[0])
  );

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

  assign cio_pwm_en_o = {NOutputs{1'b1}};

  ${module_instance_name}_core #(
    .NOutputs(NOutputs),
    .PhaseCntDw(PhaseCntDw),
    .BeatCntDw(BeatCntDw)
  ) u_pwm_core (
    .clk_core_i,
    .rst_core_ni,
    .reg2hw,
    .pwm_o       (cio_pwm_o)
  );

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  `ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)

  `ASSERT_KNOWN(CioPWMKnownO_A, cio_pwm_o)
  `ASSERT(CioPWMEnIsOneO_A, (&cio_pwm_en_o) === 1'b1)

  `ASSERT_KNOWN(RaclErrorValidKnown_A, racl_error_o.valid)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule : ${module_instance_name}
