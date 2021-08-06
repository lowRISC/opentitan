// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RISC-V Platform-Level Interrupt Controller compliant INTC
//
//   Current version doesn't support MSI interrupt but it is easy to add
//   the feature. Create one external register and connect qe signal to the
//   gateway module (as edge-triggered)
//
//   Consider to set MAX_PRIO as small number as possible. It is main factor
//   of area increase if edge-triggered counter isn't implemented.
//
// Verilog parameter
//   MAX_PRIO: Maximum value of interrupt priority

module rv_plic import rv_plic_reg_pkg::*; #(
  parameter logic [NumAlerts-1:0] AlertAsyncOn  = {NumAlerts{1'b1}},
  // OpenTitan IP standardizes on level triggered interrupts,
  // hence LevelEdgeTrig is set to all-zeroes by default.
  // Note that in case of edge-triggered interrupts, CDC handling is not
  // fully implemented yet (this would require instantiating pulse syncs
  // and routing the source clocks / resets to the PLIC).
  parameter logic [NumSrc-1:0]    LevelEdgeTrig = '0, // 0: level, 1: edge
  // derived parameter
  localparam int SRCW    = $clog2(NumSrc)
) (
  input     clk_i,
  input     rst_ni,

  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupt Sources
  input  [NumSrc-1:0] intr_src_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Interrupt notification to targets
  output [NumTarget-1:0] irq_o,
  output [SRCW-1:0]      irq_id_o [NumTarget],

  output logic [NumTarget-1:0] msip_o
);

  rv_plic_reg2hw_t reg2hw;
  rv_plic_hw2reg_t hw2reg;

  localparam int MAX_PRIO    = 7;
  localparam int PRIOW = $clog2(MAX_PRIO+1);

  logic [NumSrc-1:0] ip;

  logic [NumSrc-1:0] ie [NumTarget];

  logic [NumTarget-1:0] claim_re; // Target read indicator
  logic [SRCW-1:0]      claim_id [NumTarget];
  logic [NumSrc-1:0]    claim; // Converted from claim_re/claim_id

  logic [NumTarget-1:0] complete_we; // Target write indicator
  logic [SRCW-1:0]      complete_id [NumTarget];
  logic [NumSrc-1:0]    complete; // Converted from complete_re/complete_id

  logic [SRCW-1:0]      cc_id [NumTarget]; // Write ID

  logic [PRIOW-1:0] prio [NumSrc];

  logic [PRIOW-1:0] threshold [NumTarget];

  // Glue logic between rv_plic_reg_top and others
  assign cc_id = irq_id_o;

  always_comb begin
    claim = '0;
    for (int i = 0 ; i < NumTarget ; i++) begin
      if (claim_re[i]) claim[claim_id[i]] = 1'b1;
    end
  end
  always_comb begin
    complete = '0;
    for (int i = 0 ; i < NumTarget ; i++) begin
      if (complete_we[i]) complete[complete_id[i]] = 1'b1;
    end
  end

  //`ASSERT_PULSE(claimPulse, claim_re[i])
  //`ASSERT_PULSE(completePulse, complete_we[i])

  `ASSERT(onehot0Claim, $onehot0(claim_re))

  `ASSERT(onehot0Complete, $onehot0(complete_we))

  //////////////
  // Priority //
  //////////////
  assign prio[0] = reg2hw.prio0.q;
  assign prio[1] = reg2hw.prio1.q;
  assign prio[2] = reg2hw.prio2.q;
  assign prio[3] = reg2hw.prio3.q;
  assign prio[4] = reg2hw.prio4.q;
  assign prio[5] = reg2hw.prio5.q;
  assign prio[6] = reg2hw.prio6.q;
  assign prio[7] = reg2hw.prio7.q;
  assign prio[8] = reg2hw.prio8.q;
  assign prio[9] = reg2hw.prio9.q;
  assign prio[10] = reg2hw.prio10.q;
  assign prio[11] = reg2hw.prio11.q;
  assign prio[12] = reg2hw.prio12.q;
  assign prio[13] = reg2hw.prio13.q;
  assign prio[14] = reg2hw.prio14.q;
  assign prio[15] = reg2hw.prio15.q;
  assign prio[16] = reg2hw.prio16.q;
  assign prio[17] = reg2hw.prio17.q;
  assign prio[18] = reg2hw.prio18.q;
  assign prio[19] = reg2hw.prio19.q;
  assign prio[20] = reg2hw.prio20.q;
  assign prio[21] = reg2hw.prio21.q;
  assign prio[22] = reg2hw.prio22.q;
  assign prio[23] = reg2hw.prio23.q;
  assign prio[24] = reg2hw.prio24.q;
  assign prio[25] = reg2hw.prio25.q;
  assign prio[26] = reg2hw.prio26.q;
  assign prio[27] = reg2hw.prio27.q;
  assign prio[28] = reg2hw.prio28.q;
  assign prio[29] = reg2hw.prio29.q;
  assign prio[30] = reg2hw.prio30.q;
  assign prio[31] = reg2hw.prio31.q;

  //////////////////////
  // Interrupt Enable //
  //////////////////////
  for (genvar s = 0; s < 32; s++) begin : gen_ie0
    assign ie[0][s] = reg2hw.ie0[s].q;
  end

  ////////////////////////
  // THRESHOLD register //
  ////////////////////////
  assign threshold[0] = reg2hw.threshold0.q;

  /////////////////
  // CC register //
  /////////////////
  assign claim_re[0]    = reg2hw.cc0.re;
  assign claim_id[0]    = irq_id_o[0];
  assign complete_we[0] = reg2hw.cc0.qe;
  assign complete_id[0] = reg2hw.cc0.q;
  assign hw2reg.cc0.d   = cc_id[0];

  ///////////////////
  // MSIP register //
  ///////////////////
  assign msip_o[0] = reg2hw.msip0.q;

  ////////
  // IP //
  ////////
  for (genvar s = 0; s < 32; s++) begin : gen_ip
    assign hw2reg.ip[s].de = 1'b1; // Always write
    assign hw2reg.ip[s].d  = ip[s];
  end

  //////////////
  // Gateways //
  //////////////

  // Synchronize all incoming interrupt requests.
  logic [NumSrc-1:0] intr_src_synced;
  prim_flop_2sync #(
    .Width(NumSrc)
  ) u_prim_flop_2sync (
    .clk_i,
    .rst_ni,
    .d_i(intr_src_i),
    .q_o(intr_src_synced)
  );

  rv_plic_gateway #(
    .N_SOURCE   (NumSrc)
  ) u_gateway (
    .clk_i,
    .rst_ni,

    .src_i      (intr_src_synced),
    .le_i       (LevelEdgeTrig),

    .claim_i    (claim),
    .complete_i (complete),

    .ip_o       (ip)
  );

  ///////////////////////////////////
  // Target interrupt notification //
  ///////////////////////////////////
  for (genvar i = 0 ; i < NumTarget ; i++) begin : gen_target
    rv_plic_target #(
      .N_SOURCE    (NumSrc),
      .MAX_PRIO    (MAX_PRIO)
    ) u_target (
      .clk_i,
      .rst_ni,

      .ip_i        (ip),
      .ie_i        (ie[i]),

      .prio_i      (prio),
      .threshold_i (threshold[i]),

      .irq_o       (irq_o[i]),
      .irq_id_o    (irq_id_o[i])

    );
  end

  ////////////
  // Alerts //
  ////////////

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

  ////////////////////////
  // Register interface //
  ////////////////////////
  //  Limitation of register tool prevents the module from having flexibility to parameters
  //  So, signals are manually tied at the top.
  rv_plic_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .reg2hw,
    .hw2reg,

    .intg_err_o(alerts[0]),

    .devmode_i  (1'b1)
  );

  // Assertions
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(IrqKnownO_A, irq_o)
  `ASSERT_KNOWN(MsipKnownO_A, msip_o)
  for (genvar k = 0; k < NumTarget; k++) begin : gen_irq_id_known
    `ASSERT_KNOWN(IrqIdKnownO_A, irq_id_o[k])
  end

  // Assume
  `ASSUME(Irq0Tied_A, intr_src_i[0] == 1'b0)

endmodule

