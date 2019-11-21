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
  // derived parameter
  localparam int SRCW    = $clog2(NumSrc+1)
) (
  input     clk_i,
  input     rst_ni,

  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interrupt Sources
  input  [NumSrc-1:0] intr_src_i,

  // Interrupt notification to targets
  output [NumTarget-1:0] irq_o,
  output [SRCW-1:0]      irq_id_o [NumTarget],

  output logic [NumTarget-1:0] msip_o
);

  import rv_plic_reg_pkg::*;

  rv_plic_reg2hw_t reg2hw;
  rv_plic_hw2reg_t hw2reg;

  localparam int MAX_PRIO    = ${prio};
  localparam int PRIOW = $clog2(MAX_PRIO+1);

  logic [NumSrc-1:0] le; // 0:level 1:edge
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
      if (claim_re[i]) claim[claim_id[i] -1] = 1'b1;
    end
  end
  always_comb begin
    complete = '0;
    for (int i = 0 ; i < NumTarget ; i++) begin
      if (complete_we[i]) complete[complete_id[i] -1] = 1'b1;
    end
  end

  //`ASSERT_PULSE(claimPulse, claim_re[i], clk_i, !rst_ni)
  //`ASSERT_PULSE(completePulse, complete_we[i], clk_i, !rst_ni)

  `ASSERT(onehot0Claim, $onehot0(claim_re), clk_i, !rst_ni)

  `ASSERT(onehot0Complete, $onehot0(complete_we), clk_i, !rst_ni)

  //////////////
  // Priority //
  //////////////
% for s in range(src):
  assign prio[${s}] = reg2hw.prio${s}.q;
% endfor

  //////////////////////
  // Interrupt Enable //
  //////////////////////
% for t in range(target):
  for (genvar s = 0; s < ${src}; s++) begin : gen_ie${t}
    assign ie[${t}][s] = reg2hw.ie${t}[s].q;
  end
% endfor

  ////////////////////////
  // THRESHOLD register //
  ////////////////////////
% for t in range(target):
  assign threshold[${t}] = reg2hw.threshold${t}.q;
% endfor

  /////////////////
  // CC register //
  /////////////////
% for t in range(target):
  assign claim_re[${t}]    = reg2hw.cc${t}.re;
  assign claim_id[${t}]    = irq_id_o[${t}];
  assign complete_we[${t}] = reg2hw.cc${t}.qe;
  assign complete_id[${t}] = reg2hw.cc${t}.q;
  assign hw2reg.cc${t}.d   = cc_id[${t}];
% endfor

  ///////////////////
  // MSIP register //
  ///////////////////
% for t in range(target):
  assign msip_o[${t}] = reg2hw.msip${t}.q;
% endfor

  ////////
  // IP //
  ////////
  for (genvar s = 0; s < ${src}; s++) begin : gen_ip
    assign hw2reg.ip[s].de = 1'b1; // Always write
    assign hw2reg.ip[s].d  = ip[s];
  end

  ///////////////////////////////////
  // Detection:: 0: Level, 1: Edge //
  ///////////////////////////////////
  for (genvar s = 0; s < ${src}; s++) begin : gen_le
    assign le[s] = reg2hw.le[s].q;
  end

  //////////////
  // Gateways //
  //////////////
  rv_plic_gateway #(
    .N_SOURCE (NumSrc)
  ) u_gateway (
    .clk_i,
    .rst_ni,

    .src (intr_src_i),
    .le,

    .claim,
    .complete,

    .ip
  );

  ///////////////////////////////////
  // Target interrupt notification //
  ///////////////////////////////////
  for (genvar i = 0 ; i < NumTarget ; i++) begin : gen_target
    rv_plic_target #(
      .N_SOURCE (NumSrc),
      .MAX_PRIO (MAX_PRIO)
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

    .devmode_i  (1'b1)
  );

  // Assertions
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid, clk_i, !rst_ni)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready, clk_i, !rst_ni)
  `ASSERT_KNOWN(IrqKnownO_A, irq_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(MsipKnownO_A, msip_o, clk_i, !rst_ni)
  for (genvar k = 0; k < NumTarget; k++) begin : gen_irq_id_known
    `ASSERT_KNOWN(IrqIdKnownO_A, irq_id_o[k], clk_i, !rst_ni)
  end

endmodule
