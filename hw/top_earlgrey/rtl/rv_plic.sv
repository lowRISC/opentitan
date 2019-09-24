// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_earlgrey/doc/top_earlgrey.hjson --plic-only -o hw/top_earlgrey/

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
// verilog parameter
//   N_SOURCE: Number of interrupt sources
//   N_TARGET: Number of interrupt targets (#receptor)
//   MAX_PRIO: Maximum value of interrupt priority

module rv_plic #(
  parameter int N_SOURCE    = 54,
  parameter int N_TARGET    = 1,
  parameter     FIND_MAX    = "SEQUENTIAL", // SEQUENTIAL | MATRIX

  parameter int SRCW       = $clog2(N_SOURCE+1)  // derived parameter
) (
  input     clk_i,
  input     rst_ni,

  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupt Sources
  input  [N_SOURCE-1:0] intr_src_i,

  // Interrupt notification to targets
  output [N_TARGET-1:0] irq_o,
  output [SRCW-1:0]     irq_id_o [N_TARGET],

  output logic [N_TARGET-1:0] msip_o
);

  import rv_plic_reg_pkg::*;

  rv_plic_reg2hw_t reg2hw;
  rv_plic_hw2reg_t hw2reg;

  localparam int MAX_PRIO    = 3;
  localparam int PRIOW = $clog2(MAX_PRIO+1);

  logic [N_SOURCE-1:0] le; // 0:level 1:edge
  logic [N_SOURCE-1:0] ip;

  logic [N_SOURCE-1:0] ie [N_TARGET];

  logic [N_TARGET-1:0] claim_re; // Target read indicator
  logic [SRCW-1:0]     claim_id [N_TARGET];
  logic [N_SOURCE-1:0] claim; // Converted from claim_re/claim_id

  logic [N_TARGET-1:0] complete_we; // Target write indicator
  logic [SRCW-1:0]     complete_id [N_TARGET];
  logic [N_SOURCE-1:0] complete; // Converted from complete_re/complete_id

  logic [SRCW-1:0]     cc_id [N_TARGET]; // Write ID

  logic [PRIOW-1:0] prio [N_SOURCE];

  logic [PRIOW-1:0] threshold [N_TARGET];

  // Glue logic between rv_plic_reg_top and others
  assign cc_id = irq_id_o;

  always_comb begin
    claim = '0;
    for (int i = 0 ; i < N_TARGET ; i++) begin
      if (claim_re[i]) claim[claim_id[i] -1] = 1'b1;
    end
  end
  always_comb begin
    complete = '0;
    for (int i = 0 ; i < N_TARGET ; i++) begin
      if (complete_we[i]) complete[complete_id[i] -1] = 1'b1;
    end
  end

  //`ASSERT_PULSE(claimPulse, claim_re[i], clk_i, !rst_ni)
  //`ASSERT_PULSE(completePulse, complete_we[i], clk_i, !rst_ni)

  `ASSERT(onehot0Claim, $onehot0(claim_re), clk_i, !rst_ni)

  `ASSERT(onehot0Complete, $onehot0(complete_we), clk_i, !rst_ni)

  //////////////////////////////////////////////////////////////////////////////
  // Priority
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
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // Interrupt Enable
  assign ie[0][0] = reg2hw.ie00.e0.q;
  assign ie[0][1] = reg2hw.ie00.e1.q;
  assign ie[0][2] = reg2hw.ie00.e2.q;
  assign ie[0][3] = reg2hw.ie00.e3.q;
  assign ie[0][4] = reg2hw.ie00.e4.q;
  assign ie[0][5] = reg2hw.ie00.e5.q;
  assign ie[0][6] = reg2hw.ie00.e6.q;
  assign ie[0][7] = reg2hw.ie00.e7.q;
  assign ie[0][8] = reg2hw.ie00.e8.q;
  assign ie[0][9] = reg2hw.ie00.e9.q;
  assign ie[0][10] = reg2hw.ie00.e10.q;
  assign ie[0][11] = reg2hw.ie00.e11.q;
  assign ie[0][12] = reg2hw.ie00.e12.q;
  assign ie[0][13] = reg2hw.ie00.e13.q;
  assign ie[0][14] = reg2hw.ie00.e14.q;
  assign ie[0][15] = reg2hw.ie00.e15.q;
  assign ie[0][16] = reg2hw.ie00.e16.q;
  assign ie[0][17] = reg2hw.ie00.e17.q;
  assign ie[0][18] = reg2hw.ie00.e18.q;
  assign ie[0][19] = reg2hw.ie00.e19.q;
  assign ie[0][20] = reg2hw.ie00.e20.q;
  assign ie[0][21] = reg2hw.ie00.e21.q;
  assign ie[0][22] = reg2hw.ie00.e22.q;
  assign ie[0][23] = reg2hw.ie00.e23.q;
  assign ie[0][24] = reg2hw.ie00.e24.q;
  assign ie[0][25] = reg2hw.ie00.e25.q;
  assign ie[0][26] = reg2hw.ie00.e26.q;
  assign ie[0][27] = reg2hw.ie00.e27.q;
  assign ie[0][28] = reg2hw.ie00.e28.q;
  assign ie[0][29] = reg2hw.ie00.e29.q;
  assign ie[0][30] = reg2hw.ie00.e30.q;
  assign ie[0][31] = reg2hw.ie00.e31.q;
  assign ie[0][32] = reg2hw.ie01.e32.q;
  assign ie[0][33] = reg2hw.ie01.e33.q;
  assign ie[0][34] = reg2hw.ie01.e34.q;
  assign ie[0][35] = reg2hw.ie01.e35.q;
  assign ie[0][36] = reg2hw.ie01.e36.q;
  assign ie[0][37] = reg2hw.ie01.e37.q;
  assign ie[0][38] = reg2hw.ie01.e38.q;
  assign ie[0][39] = reg2hw.ie01.e39.q;
  assign ie[0][40] = reg2hw.ie01.e40.q;
  assign ie[0][41] = reg2hw.ie01.e41.q;
  assign ie[0][42] = reg2hw.ie01.e42.q;
  assign ie[0][43] = reg2hw.ie01.e43.q;
  assign ie[0][44] = reg2hw.ie01.e44.q;
  assign ie[0][45] = reg2hw.ie01.e45.q;
  assign ie[0][46] = reg2hw.ie01.e46.q;
  assign ie[0][47] = reg2hw.ie01.e47.q;
  assign ie[0][48] = reg2hw.ie01.e48.q;
  assign ie[0][49] = reg2hw.ie01.e49.q;
  assign ie[0][50] = reg2hw.ie01.e50.q;
  assign ie[0][51] = reg2hw.ie01.e51.q;
  assign ie[0][52] = reg2hw.ie01.e52.q;
  assign ie[0][53] = reg2hw.ie01.e53.q;
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // THRESHOLD register
  assign threshold[0] = reg2hw.threshold0.q;
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // CC register
  assign claim_re[0]    = reg2hw.cc0.re;
  assign claim_id[0]    = irq_id_o[0];
  assign complete_we[0] = reg2hw.cc0.qe;
  assign complete_id[0] = reg2hw.cc0.q;
  assign hw2reg.cc0.d   = cc_id[0];
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // MSIP register
  assign msip_o[0] = reg2hw.msip0.q;
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // IP
  assign hw2reg.ip0.p0.de = 1'b1; // Always write
  assign hw2reg.ip0.p1.de = 1'b1; // Always write
  assign hw2reg.ip0.p2.de = 1'b1; // Always write
  assign hw2reg.ip0.p3.de = 1'b1; // Always write
  assign hw2reg.ip0.p4.de = 1'b1; // Always write
  assign hw2reg.ip0.p5.de = 1'b1; // Always write
  assign hw2reg.ip0.p6.de = 1'b1; // Always write
  assign hw2reg.ip0.p7.de = 1'b1; // Always write
  assign hw2reg.ip0.p8.de = 1'b1; // Always write
  assign hw2reg.ip0.p9.de = 1'b1; // Always write
  assign hw2reg.ip0.p10.de = 1'b1; // Always write
  assign hw2reg.ip0.p11.de = 1'b1; // Always write
  assign hw2reg.ip0.p12.de = 1'b1; // Always write
  assign hw2reg.ip0.p13.de = 1'b1; // Always write
  assign hw2reg.ip0.p14.de = 1'b1; // Always write
  assign hw2reg.ip0.p15.de = 1'b1; // Always write
  assign hw2reg.ip0.p16.de = 1'b1; // Always write
  assign hw2reg.ip0.p17.de = 1'b1; // Always write
  assign hw2reg.ip0.p18.de = 1'b1; // Always write
  assign hw2reg.ip0.p19.de = 1'b1; // Always write
  assign hw2reg.ip0.p20.de = 1'b1; // Always write
  assign hw2reg.ip0.p21.de = 1'b1; // Always write
  assign hw2reg.ip0.p22.de = 1'b1; // Always write
  assign hw2reg.ip0.p23.de = 1'b1; // Always write
  assign hw2reg.ip0.p24.de = 1'b1; // Always write
  assign hw2reg.ip0.p25.de = 1'b1; // Always write
  assign hw2reg.ip0.p26.de = 1'b1; // Always write
  assign hw2reg.ip0.p27.de = 1'b1; // Always write
  assign hw2reg.ip0.p28.de = 1'b1; // Always write
  assign hw2reg.ip0.p29.de = 1'b1; // Always write
  assign hw2reg.ip0.p30.de = 1'b1; // Always write
  assign hw2reg.ip0.p31.de = 1'b1; // Always write
  assign hw2reg.ip1.p32.de = 1'b1; // Always write
  assign hw2reg.ip1.p33.de = 1'b1; // Always write
  assign hw2reg.ip1.p34.de = 1'b1; // Always write
  assign hw2reg.ip1.p35.de = 1'b1; // Always write
  assign hw2reg.ip1.p36.de = 1'b1; // Always write
  assign hw2reg.ip1.p37.de = 1'b1; // Always write
  assign hw2reg.ip1.p38.de = 1'b1; // Always write
  assign hw2reg.ip1.p39.de = 1'b1; // Always write
  assign hw2reg.ip1.p40.de = 1'b1; // Always write
  assign hw2reg.ip1.p41.de = 1'b1; // Always write
  assign hw2reg.ip1.p42.de = 1'b1; // Always write
  assign hw2reg.ip1.p43.de = 1'b1; // Always write
  assign hw2reg.ip1.p44.de = 1'b1; // Always write
  assign hw2reg.ip1.p45.de = 1'b1; // Always write
  assign hw2reg.ip1.p46.de = 1'b1; // Always write
  assign hw2reg.ip1.p47.de = 1'b1; // Always write
  assign hw2reg.ip1.p48.de = 1'b1; // Always write
  assign hw2reg.ip1.p49.de = 1'b1; // Always write
  assign hw2reg.ip1.p50.de = 1'b1; // Always write
  assign hw2reg.ip1.p51.de = 1'b1; // Always write
  assign hw2reg.ip1.p52.de = 1'b1; // Always write
  assign hw2reg.ip1.p53.de = 1'b1; // Always write
  assign hw2reg.ip0.p0.d  = ip[0];
  assign hw2reg.ip0.p1.d  = ip[1];
  assign hw2reg.ip0.p2.d  = ip[2];
  assign hw2reg.ip0.p3.d  = ip[3];
  assign hw2reg.ip0.p4.d  = ip[4];
  assign hw2reg.ip0.p5.d  = ip[5];
  assign hw2reg.ip0.p6.d  = ip[6];
  assign hw2reg.ip0.p7.d  = ip[7];
  assign hw2reg.ip0.p8.d  = ip[8];
  assign hw2reg.ip0.p9.d  = ip[9];
  assign hw2reg.ip0.p10.d  = ip[10];
  assign hw2reg.ip0.p11.d  = ip[11];
  assign hw2reg.ip0.p12.d  = ip[12];
  assign hw2reg.ip0.p13.d  = ip[13];
  assign hw2reg.ip0.p14.d  = ip[14];
  assign hw2reg.ip0.p15.d  = ip[15];
  assign hw2reg.ip0.p16.d  = ip[16];
  assign hw2reg.ip0.p17.d  = ip[17];
  assign hw2reg.ip0.p18.d  = ip[18];
  assign hw2reg.ip0.p19.d  = ip[19];
  assign hw2reg.ip0.p20.d  = ip[20];
  assign hw2reg.ip0.p21.d  = ip[21];
  assign hw2reg.ip0.p22.d  = ip[22];
  assign hw2reg.ip0.p23.d  = ip[23];
  assign hw2reg.ip0.p24.d  = ip[24];
  assign hw2reg.ip0.p25.d  = ip[25];
  assign hw2reg.ip0.p26.d  = ip[26];
  assign hw2reg.ip0.p27.d  = ip[27];
  assign hw2reg.ip0.p28.d  = ip[28];
  assign hw2reg.ip0.p29.d  = ip[29];
  assign hw2reg.ip0.p30.d  = ip[30];
  assign hw2reg.ip0.p31.d  = ip[31];
  assign hw2reg.ip1.p32.d  = ip[32];
  assign hw2reg.ip1.p33.d  = ip[33];
  assign hw2reg.ip1.p34.d  = ip[34];
  assign hw2reg.ip1.p35.d  = ip[35];
  assign hw2reg.ip1.p36.d  = ip[36];
  assign hw2reg.ip1.p37.d  = ip[37];
  assign hw2reg.ip1.p38.d  = ip[38];
  assign hw2reg.ip1.p39.d  = ip[39];
  assign hw2reg.ip1.p40.d  = ip[40];
  assign hw2reg.ip1.p41.d  = ip[41];
  assign hw2reg.ip1.p42.d  = ip[42];
  assign hw2reg.ip1.p43.d  = ip[43];
  assign hw2reg.ip1.p44.d  = ip[44];
  assign hw2reg.ip1.p45.d  = ip[45];
  assign hw2reg.ip1.p46.d  = ip[46];
  assign hw2reg.ip1.p47.d  = ip[47];
  assign hw2reg.ip1.p48.d  = ip[48];
  assign hw2reg.ip1.p49.d  = ip[49];
  assign hw2reg.ip1.p50.d  = ip[50];
  assign hw2reg.ip1.p51.d  = ip[51];
  assign hw2reg.ip1.p52.d  = ip[52];
  assign hw2reg.ip1.p53.d  = ip[53];
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // Detection:: 0: Level, 1: Edge
  assign le[0] = reg2hw.le0.le0.q;
  assign le[1] = reg2hw.le0.le1.q;
  assign le[2] = reg2hw.le0.le2.q;
  assign le[3] = reg2hw.le0.le3.q;
  assign le[4] = reg2hw.le0.le4.q;
  assign le[5] = reg2hw.le0.le5.q;
  assign le[6] = reg2hw.le0.le6.q;
  assign le[7] = reg2hw.le0.le7.q;
  assign le[8] = reg2hw.le0.le8.q;
  assign le[9] = reg2hw.le0.le9.q;
  assign le[10] = reg2hw.le0.le10.q;
  assign le[11] = reg2hw.le0.le11.q;
  assign le[12] = reg2hw.le0.le12.q;
  assign le[13] = reg2hw.le0.le13.q;
  assign le[14] = reg2hw.le0.le14.q;
  assign le[15] = reg2hw.le0.le15.q;
  assign le[16] = reg2hw.le0.le16.q;
  assign le[17] = reg2hw.le0.le17.q;
  assign le[18] = reg2hw.le0.le18.q;
  assign le[19] = reg2hw.le0.le19.q;
  assign le[20] = reg2hw.le0.le20.q;
  assign le[21] = reg2hw.le0.le21.q;
  assign le[22] = reg2hw.le0.le22.q;
  assign le[23] = reg2hw.le0.le23.q;
  assign le[24] = reg2hw.le0.le24.q;
  assign le[25] = reg2hw.le0.le25.q;
  assign le[26] = reg2hw.le0.le26.q;
  assign le[27] = reg2hw.le0.le27.q;
  assign le[28] = reg2hw.le0.le28.q;
  assign le[29] = reg2hw.le0.le29.q;
  assign le[30] = reg2hw.le0.le30.q;
  assign le[31] = reg2hw.le0.le31.q;
  assign le[32] = reg2hw.le1.le32.q;
  assign le[33] = reg2hw.le1.le33.q;
  assign le[34] = reg2hw.le1.le34.q;
  assign le[35] = reg2hw.le1.le35.q;
  assign le[36] = reg2hw.le1.le36.q;
  assign le[37] = reg2hw.le1.le37.q;
  assign le[38] = reg2hw.le1.le38.q;
  assign le[39] = reg2hw.le1.le39.q;
  assign le[40] = reg2hw.le1.le40.q;
  assign le[41] = reg2hw.le1.le41.q;
  assign le[42] = reg2hw.le1.le42.q;
  assign le[43] = reg2hw.le1.le43.q;
  assign le[44] = reg2hw.le1.le44.q;
  assign le[45] = reg2hw.le1.le45.q;
  assign le[46] = reg2hw.le1.le46.q;
  assign le[47] = reg2hw.le1.le47.q;
  assign le[48] = reg2hw.le1.le48.q;
  assign le[49] = reg2hw.le1.le49.q;
  assign le[50] = reg2hw.le1.le50.q;
  assign le[51] = reg2hw.le1.le51.q;
  assign le[52] = reg2hw.le1.le52.q;
  assign le[53] = reg2hw.le1.le53.q;
  //----------------------------------------------------------------------------

  // Gateways
  rv_plic_gateway #(
    .N_SOURCE (N_SOURCE)
  ) u_gateway (
    .clk_i,
    .rst_ni,

    .src (intr_src_i),
    .le,

    .claim,
    .complete,

    .ip
  );


  // Target interrupt notification
  for (genvar i = 0 ; i < N_TARGET ; i++) begin : gen_target
    rv_plic_target #(
      .N_SOURCE (N_SOURCE),
      .MAX_PRIO (MAX_PRIO),
      .ALGORITHM(FIND_MAX)
    ) u_target (
      .clk_i,
      .rst_ni,

      .ip,
      .ie        (ie[i]),

      .prio,
      .threshold (threshold[i]),

      .irq       (irq_o[i]),
      .irq_id    (irq_id_o[i])

    );
  end

  // Register interface
  //  Limitation of register tool prevents the module from having flexibility to parameters
  //  So, signals are manually tied at the top.
  rv_plic_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .reg2hw,
    .hw2reg,

    .devmode_i  (1'b1)
  );

endmodule
