// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C top level wrapper file

`include "prim_assert.sv"

module socdbg_ctrl
  import otp_ctrl_pkg::*;
  import rom_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import socdbg_ctrl_pkg::*;
  import socdbg_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input                             clk_i,
  input                             rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t         core_tl_i,
  output tlul_pkg::tl_d2h_t         core_tl_o,

  input  tlul_pkg::tl_h2d_t         jtag_tl_i,
  output tlul_pkg::tl_d2h_t         jtag_tl_o,

  // Custom Interface
  input  soc_dbg_state_t            soc_dbg_state_i,
  output soc_dbg_policy_t           socdbg_policy_bus_o,

  // A0 functionality for risk mitigation
  // Halts CPU boot in early lifecycle stages after reset based on an external signal
  // Halt functionality disappears in the production lifecycle
  input  logic                      halt_cpu_boot_i,
  output rom_ctrl_pkg::pwrmgr_data_t continue_cpu_boot_o,

  // Lifecycle broadcast inputs
  // SEC_CM: LC_CTRL.INTERSIG.MUBI
  input  lc_ctrl_pkg::lc_tx_t       lc_creator_seed_sw_rw_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_seed_hw_rd_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_hw_debug_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_escalate_en_i,
  input  lc_ctrl_pkg::lc_tx_t       lc_check_byp_en_i,
  // Alerts

  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Generic IO

  // Interrupts
  output logic                      intr_debug_attention_o
);

  socdbg_ctrl_core_reg2hw_t core_reg2hw;
  socdbg_ctrl_core_hw2reg_t core_hw2reg;
  socdbg_ctrl_jtag_hw2reg_t jtag_hw2reg; // Read

  assign socdbg_policy_bus_o.policy  = core_reg2hw.debug_policy_ctrl.q;   // FIXME implement MUBI
  assign socdbg_policy_bus_o.valid   = core_reg2hw.debug_policy_valid.q;  // FIXME implement MUBI

  assign continue_cpu_boot_o         = PWRMGR_DATA_DEFAULT;   // FIXME to be tied to
                                                              // the external pin based controls

  //assign core_hw2reg.status.status0.d     = '0;                    // FIXME implement
  //assign core_hw2reg.status.status1.d     = '0;                    // FIXME implement

  logic [NumAlerts-1:0] alert_test, alerts;

  // IBEX core side TL-UL device port
  //
  socdbg_ctrl_core_reg_top u_core_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (core_tl_i),
    .tl_o       (core_tl_o),
    .reg2hw     (core_reg2hw),
    .hw2reg     (core_hw2reg),
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (core_tl_intg_err),
    .devmode_i  (1'b1)
  );

  // The status mailbox register written by IBEX firmware is reflected into the JTAG status regsiter
  // JTAG user shall query this status register
  assign jtag_hw2reg.jtag_status = core_reg2hw.status_mbx;

  // JTAG host side TL-UL device port
  //
  socdbg_ctrl_jtag_reg_top u_jtag_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (jtag_tl_i),
    .tl_o       (jtag_tl_o),
  //.reg2hw     (jtag_reg2hw),
    .hw2reg     (jtag_hw2reg),      // assigned to status mailbox
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (jtag_tl_intg_err),
    .devmode_i  (1'b1)
  );

  // 'OR' fatal alert indications from TL-UL integrity
  // checks on the core and jtag interfaces
  assign alerts[0] = core_tl_intg_err | jtag_tl_intg_err;

  assign alert_test = {
    core_reg2hw.alert_test.q &
    core_reg2hw.alert_test.qe
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

  logic scl_int;
  logic event_debug_attention;

  assign event_debug_attention = 0; // placeholder comportable interrupt event

  prim_intr_hw #(.Width(1)) socdbg_ctrl_intr (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_debug_attention),
    .reg2hw_intr_enable_q_i (core_reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (core_reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (core_reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (core_reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (core_hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (core_hw2reg.intr_state.d),
    .intr_o                 (intr_debug_attention_o)
  );


  `ASSERT_KNOWN(CoreTlDValidKnownO_A, core_tl_o.d_valid)
  `ASSERT_KNOWN(CoreTlAReadyKnownO_A, core_tl_o.a_ready)
  `ASSERT_KNOWN(JtagTlDValidKnownO_A, jtag_tl_o.d_valid)
  `ASSERT_KNOWN(JtagTlAReadyKnownO_A, jtag_tl_o.a_ready)
  `ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)
  `ASSERT_KNOWN(IntrHostTimeoutKnownO_A, intr_debug_attention_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_core_reg, alert_tx_o[0])
endmodule
