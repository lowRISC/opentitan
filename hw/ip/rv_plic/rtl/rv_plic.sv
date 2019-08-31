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
  parameter int N_SOURCE    = 32,
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

  localparam int MAX_PRIO    = 7;
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
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // Interrupt Enable
  assign ie[0][0] = reg2hw.ie0.e0.q;
  assign ie[0][1] = reg2hw.ie0.e1.q;
  assign ie[0][2] = reg2hw.ie0.e2.q;
  assign ie[0][3] = reg2hw.ie0.e3.q;
  assign ie[0][4] = reg2hw.ie0.e4.q;
  assign ie[0][5] = reg2hw.ie0.e5.q;
  assign ie[0][6] = reg2hw.ie0.e6.q;
  assign ie[0][7] = reg2hw.ie0.e7.q;
  assign ie[0][8] = reg2hw.ie0.e8.q;
  assign ie[0][9] = reg2hw.ie0.e9.q;
  assign ie[0][10] = reg2hw.ie0.e10.q;
  assign ie[0][11] = reg2hw.ie0.e11.q;
  assign ie[0][12] = reg2hw.ie0.e12.q;
  assign ie[0][13] = reg2hw.ie0.e13.q;
  assign ie[0][14] = reg2hw.ie0.e14.q;
  assign ie[0][15] = reg2hw.ie0.e15.q;
  assign ie[0][16] = reg2hw.ie0.e16.q;
  assign ie[0][17] = reg2hw.ie0.e17.q;
  assign ie[0][18] = reg2hw.ie0.e18.q;
  assign ie[0][19] = reg2hw.ie0.e19.q;
  assign ie[0][20] = reg2hw.ie0.e20.q;
  assign ie[0][21] = reg2hw.ie0.e21.q;
  assign ie[0][22] = reg2hw.ie0.e22.q;
  assign ie[0][23] = reg2hw.ie0.e23.q;
  assign ie[0][24] = reg2hw.ie0.e24.q;
  assign ie[0][25] = reg2hw.ie0.e25.q;
  assign ie[0][26] = reg2hw.ie0.e26.q;
  assign ie[0][27] = reg2hw.ie0.e27.q;
  assign ie[0][28] = reg2hw.ie0.e28.q;
  assign ie[0][29] = reg2hw.ie0.e29.q;
  assign ie[0][30] = reg2hw.ie0.e30.q;
  assign ie[0][31] = reg2hw.ie0.e31.q;
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
  assign hw2reg.ip.p0.de = 1'b1; // Always write
  assign hw2reg.ip.p1.de = 1'b1; // Always write
  assign hw2reg.ip.p2.de = 1'b1; // Always write
  assign hw2reg.ip.p3.de = 1'b1; // Always write
  assign hw2reg.ip.p4.de = 1'b1; // Always write
  assign hw2reg.ip.p5.de = 1'b1; // Always write
  assign hw2reg.ip.p6.de = 1'b1; // Always write
  assign hw2reg.ip.p7.de = 1'b1; // Always write
  assign hw2reg.ip.p8.de = 1'b1; // Always write
  assign hw2reg.ip.p9.de = 1'b1; // Always write
  assign hw2reg.ip.p10.de = 1'b1; // Always write
  assign hw2reg.ip.p11.de = 1'b1; // Always write
  assign hw2reg.ip.p12.de = 1'b1; // Always write
  assign hw2reg.ip.p13.de = 1'b1; // Always write
  assign hw2reg.ip.p14.de = 1'b1; // Always write
  assign hw2reg.ip.p15.de = 1'b1; // Always write
  assign hw2reg.ip.p16.de = 1'b1; // Always write
  assign hw2reg.ip.p17.de = 1'b1; // Always write
  assign hw2reg.ip.p18.de = 1'b1; // Always write
  assign hw2reg.ip.p19.de = 1'b1; // Always write
  assign hw2reg.ip.p20.de = 1'b1; // Always write
  assign hw2reg.ip.p21.de = 1'b1; // Always write
  assign hw2reg.ip.p22.de = 1'b1; // Always write
  assign hw2reg.ip.p23.de = 1'b1; // Always write
  assign hw2reg.ip.p24.de = 1'b1; // Always write
  assign hw2reg.ip.p25.de = 1'b1; // Always write
  assign hw2reg.ip.p26.de = 1'b1; // Always write
  assign hw2reg.ip.p27.de = 1'b1; // Always write
  assign hw2reg.ip.p28.de = 1'b1; // Always write
  assign hw2reg.ip.p29.de = 1'b1; // Always write
  assign hw2reg.ip.p30.de = 1'b1; // Always write
  assign hw2reg.ip.p31.de = 1'b1; // Always write
  assign hw2reg.ip.p0.d  = ip[0];
  assign hw2reg.ip.p1.d  = ip[1];
  assign hw2reg.ip.p2.d  = ip[2];
  assign hw2reg.ip.p3.d  = ip[3];
  assign hw2reg.ip.p4.d  = ip[4];
  assign hw2reg.ip.p5.d  = ip[5];
  assign hw2reg.ip.p6.d  = ip[6];
  assign hw2reg.ip.p7.d  = ip[7];
  assign hw2reg.ip.p8.d  = ip[8];
  assign hw2reg.ip.p9.d  = ip[9];
  assign hw2reg.ip.p10.d  = ip[10];
  assign hw2reg.ip.p11.d  = ip[11];
  assign hw2reg.ip.p12.d  = ip[12];
  assign hw2reg.ip.p13.d  = ip[13];
  assign hw2reg.ip.p14.d  = ip[14];
  assign hw2reg.ip.p15.d  = ip[15];
  assign hw2reg.ip.p16.d  = ip[16];
  assign hw2reg.ip.p17.d  = ip[17];
  assign hw2reg.ip.p18.d  = ip[18];
  assign hw2reg.ip.p19.d  = ip[19];
  assign hw2reg.ip.p20.d  = ip[20];
  assign hw2reg.ip.p21.d  = ip[21];
  assign hw2reg.ip.p22.d  = ip[22];
  assign hw2reg.ip.p23.d  = ip[23];
  assign hw2reg.ip.p24.d  = ip[24];
  assign hw2reg.ip.p25.d  = ip[25];
  assign hw2reg.ip.p26.d  = ip[26];
  assign hw2reg.ip.p27.d  = ip[27];
  assign hw2reg.ip.p28.d  = ip[28];
  assign hw2reg.ip.p29.d  = ip[29];
  assign hw2reg.ip.p30.d  = ip[30];
  assign hw2reg.ip.p31.d  = ip[31];
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // Detection:: 0: Level, 1: Edge
  assign le[0] = reg2hw.le.le0.q;
  assign le[1] = reg2hw.le.le1.q;
  assign le[2] = reg2hw.le.le2.q;
  assign le[3] = reg2hw.le.le3.q;
  assign le[4] = reg2hw.le.le4.q;
  assign le[5] = reg2hw.le.le5.q;
  assign le[6] = reg2hw.le.le6.q;
  assign le[7] = reg2hw.le.le7.q;
  assign le[8] = reg2hw.le.le8.q;
  assign le[9] = reg2hw.le.le9.q;
  assign le[10] = reg2hw.le.le10.q;
  assign le[11] = reg2hw.le.le11.q;
  assign le[12] = reg2hw.le.le12.q;
  assign le[13] = reg2hw.le.le13.q;
  assign le[14] = reg2hw.le.le14.q;
  assign le[15] = reg2hw.le.le15.q;
  assign le[16] = reg2hw.le.le16.q;
  assign le[17] = reg2hw.le.le17.q;
  assign le[18] = reg2hw.le.le18.q;
  assign le[19] = reg2hw.le.le19.q;
  assign le[20] = reg2hw.le.le20.q;
  assign le[21] = reg2hw.le.le21.q;
  assign le[22] = reg2hw.le.le22.q;
  assign le[23] = reg2hw.le.le23.q;
  assign le[24] = reg2hw.le.le24.q;
  assign le[25] = reg2hw.le.le25.q;
  assign le[26] = reg2hw.le.le26.q;
  assign le[27] = reg2hw.le.le27.q;
  assign le[28] = reg2hw.le.le28.q;
  assign le[29] = reg2hw.le.le29.q;
  assign le[30] = reg2hw.le.le30.q;
  assign le[31] = reg2hw.le.le31.q;
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
    .hw2reg
  );

endmodule

