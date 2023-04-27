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

  localparam int MAX_PRIO    = 3;
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

  logic [NumSrc-1:0][PRIOW-1:0] prio;

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
  assign prio[32] = reg2hw.prio32.q;
  assign prio[33] = reg2hw.prio33.q;
  assign prio[34] = reg2hw.prio34.q;
  assign prio[35] = reg2hw.prio35.q;
  assign prio[36] = reg2hw.prio36.q;
  assign prio[37] = reg2hw.prio37.q;
  assign prio[38] = reg2hw.prio38.q;
  assign prio[39] = reg2hw.prio39.q;
  assign prio[40] = reg2hw.prio40.q;
  assign prio[41] = reg2hw.prio41.q;
  assign prio[42] = reg2hw.prio42.q;
  assign prio[43] = reg2hw.prio43.q;
  assign prio[44] = reg2hw.prio44.q;
  assign prio[45] = reg2hw.prio45.q;
  assign prio[46] = reg2hw.prio46.q;
  assign prio[47] = reg2hw.prio47.q;
  assign prio[48] = reg2hw.prio48.q;
  assign prio[49] = reg2hw.prio49.q;
  assign prio[50] = reg2hw.prio50.q;
  assign prio[51] = reg2hw.prio51.q;
  assign prio[52] = reg2hw.prio52.q;
  assign prio[53] = reg2hw.prio53.q;
  assign prio[54] = reg2hw.prio54.q;
  assign prio[55] = reg2hw.prio55.q;
  assign prio[56] = reg2hw.prio56.q;
  assign prio[57] = reg2hw.prio57.q;
  assign prio[58] = reg2hw.prio58.q;
  assign prio[59] = reg2hw.prio59.q;
  assign prio[60] = reg2hw.prio60.q;
  assign prio[61] = reg2hw.prio61.q;
  assign prio[62] = reg2hw.prio62.q;
  assign prio[63] = reg2hw.prio63.q;
  assign prio[64] = reg2hw.prio64.q;
  assign prio[65] = reg2hw.prio65.q;
  assign prio[66] = reg2hw.prio66.q;
  assign prio[67] = reg2hw.prio67.q;
  assign prio[68] = reg2hw.prio68.q;
  assign prio[69] = reg2hw.prio69.q;
  assign prio[70] = reg2hw.prio70.q;
  assign prio[71] = reg2hw.prio71.q;
  assign prio[72] = reg2hw.prio72.q;
  assign prio[73] = reg2hw.prio73.q;
  assign prio[74] = reg2hw.prio74.q;
  assign prio[75] = reg2hw.prio75.q;
  assign prio[76] = reg2hw.prio76.q;
  assign prio[77] = reg2hw.prio77.q;
  assign prio[78] = reg2hw.prio78.q;
  assign prio[79] = reg2hw.prio79.q;
  assign prio[80] = reg2hw.prio80.q;
  assign prio[81] = reg2hw.prio81.q;
  assign prio[82] = reg2hw.prio82.q;
  assign prio[83] = reg2hw.prio83.q;
  assign prio[84] = reg2hw.prio84.q;
  assign prio[85] = reg2hw.prio85.q;
  assign prio[86] = reg2hw.prio86.q;
  assign prio[87] = reg2hw.prio87.q;
  assign prio[88] = reg2hw.prio88.q;
  assign prio[89] = reg2hw.prio89.q;
  assign prio[90] = reg2hw.prio90.q;
  assign prio[91] = reg2hw.prio91.q;
  assign prio[92] = reg2hw.prio92.q;
  assign prio[93] = reg2hw.prio93.q;
  assign prio[94] = reg2hw.prio94.q;
  assign prio[95] = reg2hw.prio95.q;
  assign prio[96] = reg2hw.prio96.q;
  assign prio[97] = reg2hw.prio97.q;
  assign prio[98] = reg2hw.prio98.q;
  assign prio[99] = reg2hw.prio99.q;
  assign prio[100] = reg2hw.prio100.q;
  assign prio[101] = reg2hw.prio101.q;
  assign prio[102] = reg2hw.prio102.q;
  assign prio[103] = reg2hw.prio103.q;
  assign prio[104] = reg2hw.prio104.q;
  assign prio[105] = reg2hw.prio105.q;
  assign prio[106] = reg2hw.prio106.q;
  assign prio[107] = reg2hw.prio107.q;
  assign prio[108] = reg2hw.prio108.q;
  assign prio[109] = reg2hw.prio109.q;
  assign prio[110] = reg2hw.prio110.q;
  assign prio[111] = reg2hw.prio111.q;
  assign prio[112] = reg2hw.prio112.q;
  assign prio[113] = reg2hw.prio113.q;
  assign prio[114] = reg2hw.prio114.q;
  assign prio[115] = reg2hw.prio115.q;
  assign prio[116] = reg2hw.prio116.q;
  assign prio[117] = reg2hw.prio117.q;
  assign prio[118] = reg2hw.prio118.q;
  assign prio[119] = reg2hw.prio119.q;
  assign prio[120] = reg2hw.prio120.q;
  assign prio[121] = reg2hw.prio121.q;
  assign prio[122] = reg2hw.prio122.q;
  assign prio[123] = reg2hw.prio123.q;
  assign prio[124] = reg2hw.prio124.q;
  assign prio[125] = reg2hw.prio125.q;
  assign prio[126] = reg2hw.prio126.q;
  assign prio[127] = reg2hw.prio127.q;
  assign prio[128] = reg2hw.prio128.q;
  assign prio[129] = reg2hw.prio129.q;
  assign prio[130] = reg2hw.prio130.q;
  assign prio[131] = reg2hw.prio131.q;
  assign prio[132] = reg2hw.prio132.q;
  assign prio[133] = reg2hw.prio133.q;
  assign prio[134] = reg2hw.prio134.q;
  assign prio[135] = reg2hw.prio135.q;
  assign prio[136] = reg2hw.prio136.q;
  assign prio[137] = reg2hw.prio137.q;
  assign prio[138] = reg2hw.prio138.q;
  assign prio[139] = reg2hw.prio139.q;
  assign prio[140] = reg2hw.prio140.q;
  assign prio[141] = reg2hw.prio141.q;
  assign prio[142] = reg2hw.prio142.q;
  assign prio[143] = reg2hw.prio143.q;
  assign prio[144] = reg2hw.prio144.q;
  assign prio[145] = reg2hw.prio145.q;
  assign prio[146] = reg2hw.prio146.q;
  assign prio[147] = reg2hw.prio147.q;
  assign prio[148] = reg2hw.prio148.q;
  assign prio[149] = reg2hw.prio149.q;
  assign prio[150] = reg2hw.prio150.q;
  assign prio[151] = reg2hw.prio151.q;
  assign prio[152] = reg2hw.prio152.q;
  assign prio[153] = reg2hw.prio153.q;
  assign prio[154] = reg2hw.prio154.q;
  assign prio[155] = reg2hw.prio155.q;
  assign prio[156] = reg2hw.prio156.q;
  assign prio[157] = reg2hw.prio157.q;
  assign prio[158] = reg2hw.prio158.q;
  assign prio[159] = reg2hw.prio159.q;
  assign prio[160] = reg2hw.prio160.q;
  assign prio[161] = reg2hw.prio161.q;
  assign prio[162] = reg2hw.prio162.q;
  assign prio[163] = reg2hw.prio163.q;
  assign prio[164] = reg2hw.prio164.q;
  assign prio[165] = reg2hw.prio165.q;
  assign prio[166] = reg2hw.prio166.q;
  assign prio[167] = reg2hw.prio167.q;
  assign prio[168] = reg2hw.prio168.q;
  assign prio[169] = reg2hw.prio169.q;
  assign prio[170] = reg2hw.prio170.q;
  assign prio[171] = reg2hw.prio171.q;
  assign prio[172] = reg2hw.prio172.q;
  assign prio[173] = reg2hw.prio173.q;
  assign prio[174] = reg2hw.prio174.q;
  assign prio[175] = reg2hw.prio175.q;
  assign prio[176] = reg2hw.prio176.q;
  assign prio[177] = reg2hw.prio177.q;
  assign prio[178] = reg2hw.prio178.q;
  assign prio[179] = reg2hw.prio179.q;
  assign prio[180] = reg2hw.prio180.q;
  assign prio[181] = reg2hw.prio181.q;
  assign prio[182] = reg2hw.prio182.q;
  assign prio[183] = reg2hw.prio183.q;
  assign prio[184] = reg2hw.prio184.q;

  //////////////////////
  // Interrupt Enable //
  //////////////////////
  for (genvar s = 0; s < 185; s++) begin : gen_ie0
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
  for (genvar s = 0; s < 185; s++) begin : gen_ip
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
      .alert_req_i   ( alerts[i]     ),
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

    // SEC_CM: BUS.INTEGRITY
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

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
