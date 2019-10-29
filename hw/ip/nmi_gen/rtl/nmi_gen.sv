// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// NMI generator. This is a simple helper unit that wraps the escalation signal
// receivers and converts them into interrupts such that they can be tested in system.
// See also alert handler documentation for more context.

module nmi_gen import prim_pkg::*; #(
  // leave constant
  localparam int unsigned N_ESC_SEV = 4
) (
  input                           clk_i,
  input                           rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t       tl_i,
  output tlul_pkg::tl_d2h_t       tl_o,
  // Interrupt Requests
  output logic                    intr_esc0_o,
  output logic                    intr_esc1_o,
  output logic                    intr_esc2_o,
  output logic                    intr_esc3_o,
  // Escalation outputs
  input  esc_tx_t [N_ESC_SEV-1:0] esc_tx_i,
  output esc_rx_t [N_ESC_SEV-1:0] esc_rx_o
);

  //////////////////////
  // Regfile instance //
  //////////////////////

  logic [N_ESC_SEV-1:0] esc_en;
  nmi_gen_reg_pkg::nmi_gen_reg2hw_t reg2hw;
  nmi_gen_reg_pkg::nmi_gen_hw2reg_t hw2reg;

  nmi_gen_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  ////////////////
  // Interrupts //
  ////////////////

  prim_intr_hw #(
    .Width(1)
  ) i_intr_esc0 (
    .event_intr_i           ( esc_en[0]                  ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.esc0.q  ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.esc0.q    ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.esc0.qe   ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.esc0.q   ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.esc0.de  ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.esc0.d   ),
    .intr_o                 ( intr_esc0_o                )
  );

  prim_intr_hw #(
    .Width(1)
  ) i_intr_esc1 (
    .event_intr_i           ( esc_en[1]                  ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.esc1.q  ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.esc1.q    ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.esc1.qe   ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.esc1.q   ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.esc1.de  ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.esc1.d   ),
    .intr_o                 ( intr_esc1_o                )
  );

  prim_intr_hw #(
    .Width(1)
  ) i_intr_esc2 (
    .event_intr_i           ( esc_en[2]                  ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.esc2.q  ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.esc2.q    ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.esc2.qe   ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.esc2.q   ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.esc2.de  ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.esc2.d   ),
    .intr_o                 ( intr_esc2_o                )
  );

  prim_intr_hw #(
    .Width(1)
  ) i_intr_esc3 (
    .event_intr_i           ( esc_en[3]                  ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.esc3.q  ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.esc3.q    ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.esc3.qe   ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.esc3.q   ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.esc3.de  ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.esc3.d   ),
    .intr_o                 ( intr_esc3_o                )
  );

  /////////////////////////////////////////
  // Connect escalation signal receivers //
  /////////////////////////////////////////
  for (genvar k = 0; k < N_ESC_SEV; k++) begin : gen_esc_sev
    prim_esc_receiver i_prim_esc_receiver (
      .clk_i,
      .rst_ni,
      .esc_en_o ( esc_en[k]   ),
      .esc_rx_o ( esc_rx_o[k] ),
      .esc_tx_i ( esc_tx_i[k] )
    );
  end : gen_esc_sev

endmodule : nmi_gen
