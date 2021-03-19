// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Assertions for ping timer in alert handler. Intended to use with
// a formal tool.

`include "prim_assert.sv"

module alert_handler_ping_timer_assert_fpv import alert_pkg::*; (
  input                   clk_i,
  input                   rst_ni,
  input                   entropy_i,
  input                   en_i,
  input [NAlerts-1:0]     alert_en_i,
  input [PING_CNT_DW-1:0] ping_timeout_cyc_i,
  input [PING_CNT_DW-1:0] wait_cyc_mask_i,
  input [NAlerts-1:0]     alert_ping_en_o,
  input [N_ESC_SEV-1:0]   esc_ping_en_o,
  input [NAlerts-1:0]     alert_ping_ok_i,
  input [N_ESC_SEV-1:0]   esc_ping_ok_i,
  input                   alert_ping_fail_o,
  input                   esc_ping_fail_o
);

  logic [N_ESC_SEV+NAlerts-1:0] ping_en_vector, ping_en_mask, ping_ok_vector;

  assign ping_en_vector = {esc_ping_en_o, alert_ping_en_o};
  assign ping_en_mask   = {N_ESC_SEV'('1), alert_en_i};
  assign ping_ok_vector = {esc_ping_ok_i, alert_ping_ok_i};

  /////////////////
  // Assumptions //
  /////////////////

  // symbolic variable. we want to assess all valid indices
  int unsigned ping_en_sel;
  `ASSUME_FPV(PingEnSelRange_M, ping_en_sel >= 0 && ping_en_sel < (N_ESC_SEV+NAlerts))
  `ASSUME_FPV(PingEnSelStable_M, ##1 $stable(ping_en_sel))
  // assume that the alert enable configuration is locked once en_i is high
  // this is ensured by the CSR regfile on the outside
  `ASSUME_FPV(ConfigLocked0_M, en_i |-> ($stable(alert_en_i) [*]))
  `ASSUME_FPV(ConfigLocked1_M, en_i |-> ($stable(ping_timeout_cyc_i) [*]))
  // enable stays high forever, once it has been asserted
  // this can be enabled in DV as well
  `ASSUME(ConfigLocked2_M, en_i |-> (##1 en_i) [*])
  // reduce state space by reducing length of wait period
  `ASSUME_FPV(WaitPeriod_M, wait_cyc_mask_i == 7)

  ////////////////////////
  // Forward Assertions //
  ////////////////////////

  // no pings on disabled alerts
  `ASSERT(DisabledNoAlertPings_A, ((~alert_en_i) & alert_ping_en_o) == 0)
  // no pings when not enabled
  `ASSERT(NoPingsWhenDisabled0_A, !en_i |-> !alert_ping_en_o)
  `ASSERT(NoPingsWhenDisabled1_A, !en_i |-> !esc_ping_en_o)
  `ASSERT(NoPingsWhenDisabled2_A, en_i && !ping_en_mask[ping_en_sel] |->
      !ping_en_vector[ping_en_sel])

  // spurious pings (i.e. pings that where not requested)
  // on alert channels
  `ASSERT(SpuriousPingsDetected0_A, en_i && !ping_en_vector[ping_en_sel] &&
      ping_ok_vector[ping_en_sel] && ping_en_sel < NAlerts |->
      alert_ping_fail_o)
  // on escalation channels
  `ASSERT(SpuriousPingsDetected1_A, en_i && !ping_en_vector[ping_en_sel] &&
      ping_ok_vector[ping_en_sel] && ping_en_sel >= NAlerts |->
      esc_ping_fail_o)
  // response must be one hot
  `ASSERT(SpuriousPingsDetected2_A, en_i && !$onehot0(ping_ok_vector) |->
      esc_ping_fail_o || alert_ping_fail_o)

  /////////////////////////
  // Backward Assertions //
  /////////////////////////

  // no pings when not enabled
  `ASSERT(NoPingsWhenDisabledBkwd0_A, alert_ping_en_o |-> en_i)
  `ASSERT(NoPingsWhenDisabledBkwd1_A, esc_ping_en_o   |-> en_i)

  // spurious pings (i.e. pings that where not requested)
  // on alert channels
  `ASSERT(SpuriousPingsDetectedBkwd0_A, !alert_ping_fail_o |->
      !en_i || ping_en_vector[ping_en_sel] ||
      !ping_ok_vector[ping_en_sel] || ping_en_sel >= NAlerts)
  // on escalation channels
  `ASSERT(SpuriousPingsDetectedBkwd1_A, !esc_ping_fail_o |->
      !en_i || ping_en_vector[ping_en_sel] ||
      !ping_ok_vector[ping_en_sel] || ping_en_sel < NAlerts)
  // response must be one hot
  `ASSERT(SpuriousPingsDetectedBkwd2_A, !esc_ping_fail_o && !alert_ping_fail_o |->
      !en_i || $onehot0(ping_ok_vector))

  //////////////////////////////////////////////////////////
  // Currently not Tested in FPV due to large state space //
  //////////////////////////////////////////////////////////

  // 1) if an alert is enabled, it should be pinged eventually
  // when entropy input is disabled
  // 2) ping ok within timeout -> ok
  // 3) ping ok after timeout -> alert
  // 4) no ping response -> alert

endmodule : alert_handler_ping_timer_assert_fpv
