// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// OTP Controller top.
//

`include "prim_assert.sv"

module otp_ctrl
import otp_ctrl_pkg::*;
import otp_ctrl_reg_pkg::*;
(
    input                                             clk_i,
    input                                             rst_ni,
    // TODO: signals to AST
    // Bus Interface (device)
    input  tlul_pkg::tl_h2d_t                         tl_i,
    output tlul_pkg::tl_d2h_t                         tl_o,
    // Interrupt Requests
    output logic                                      intr_otp_access_done_o,
    output logic                                      intr_otp_ctrl_err_o,
    // Alerts
    input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
    output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
    // Power manager interface
    input  pwr_otp_init_req_t                         pwr_otp_init_req_i,
    output pwr_otp_init_rsp_t                         pwr_otp_init_rsp_o,
    output otp_pwr_state_t                            otp_pwr_state_o,
    // Lifecycle transition command interface
    input  lc_otp_program_req_t                       lc_otp_program_req_i,
    output lc_otp_program_rsp_t                       lc_otp_program_rsp_o,
    // Lifecycle broadcast inputs
    input  lc_tx_t                                    lc_provision_en_i,
    input  lc_tx_t                                    lc_test_en_i,
    // OTP broadcast outputs
    output otp_lc_data_t                              otp_lc_data_o,
    output keymgr_key_t                               otp_keymgr_key_o,
    output flash_key_t                                otp_flash_key_o
    // TODO: other hardware broadcast outputs
);

  //////////////////////////////////
  // Regfile Breakout and Mapping //
  //////////////////////////////////

  tlul_pkg::tl_h2d_t tl_win_h2d[2];
  tlul_pkg::tl_d2h_t tl_win_d2h[2];

  otp_ctrl_reg_pkg::otp_ctrl_reg2hw_t reg2hw;
  otp_ctrl_reg_pkg::otp_ctrl_hw2reg_t hw2reg;

  otp_ctrl_reg_top u_reg (
      .clk_i,
      .rst_ni,
      .tl_i,
      .tl_o,
      .tl_win_o (tl_win_h2d),
      .tl_win_i (tl_win_d2h),
      .reg2hw   (reg2hw),
      .hw2reg   (hw2reg),
      .devmode_i(1'b1)
  );

  ////////////////
  // Interrupts //
  ////////////////

  logic otp_access_done;
  logic otp_ctrl_err;

  // dummy connections
  assign otp_access_done = reg2hw.direct_access_size.q[0];
  assign otp_ctrl_err = reg2hw.direct_access_size.q[1];

  prim_intr_hw #(
      .Width(1)
  ) i_intr_esc0 (
      .event_intr_i          (otp_access_done),
      .reg2hw_intr_enable_q_i(reg2hw.intr_enable.otp_access_done.q),
      .reg2hw_intr_test_q_i  (reg2hw.intr_test.otp_access_done.q),
      .reg2hw_intr_test_qe_i (reg2hw.intr_test.otp_access_done.qe),
      .reg2hw_intr_state_q_i (reg2hw.intr_state.otp_access_done.q),
      .hw2reg_intr_state_de_o(hw2reg.intr_state.otp_access_done.de),
      .hw2reg_intr_state_d_o (hw2reg.intr_state.otp_access_done.d),
      .intr_o                (intr_otp_access_done_o)
  );

  prim_intr_hw #(
      .Width(1)
  ) i_intr_esc1 (
      .event_intr_i          (otp_ctrl_err),
      .reg2hw_intr_enable_q_i(reg2hw.intr_enable.otp_ctrl_err.q),
      .reg2hw_intr_test_q_i  (reg2hw.intr_test.otp_ctrl_err.q),
      .reg2hw_intr_test_qe_i (reg2hw.intr_test.otp_ctrl_err.qe),
      .reg2hw_intr_state_q_i (reg2hw.intr_state.otp_ctrl_err.q),
      .hw2reg_intr_state_de_o(hw2reg.intr_state.otp_ctrl_err.de),
      .hw2reg_intr_state_d_o (hw2reg.intr_state.otp_ctrl_err.d),
      .intr_o                (intr_otp_ctrl_err_o)
  );

  ///////////////////
  // Alert Senders //
  ///////////////////

  logic parity_mismatch;
  logic digest_mismatch;

  // dummy connections
  assign parity_mismatch = reg2hw.direct_access_cmd.read.q && reg2hw.direct_access_cmd.read.qe;
  assign digest_mismatch = reg2hw.direct_access_cmd.write.q && reg2hw.direct_access_cmd.write.qe;

  prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[0])
  ) i_prim_alert_sender0 (
      .clk_i,
      .rst_ni,
      .alert_i   (parity_mismatch),
      .alert_rx_i(alert_rx_i[0]),
      .alert_tx_o(alert_tx_o[0])
  );

  prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[1])
  ) i_prim_alert_sender1 (
      .clk_i,
      .rst_ni,
      .alert_i   (digest_mismatch),
      .alert_rx_i(alert_rx_i[1]),
      .alert_tx_o(alert_tx_o[1])
  );

  ///////////////
  // OTP Macro //
  ///////////////

  localparam int OtpWidth = 8;
  localparam int OtpDepth = 1024;
  localparam int OtpAddrWidth = $clog2(OtpDepth);
  localparam int OtpErrWidth = 8;

  logic otp_init_req, otp_init_done;
  logic otp_err_valid;
  logic [OtpErrWidth-1:0] otp_err_code;
  logic otp_valid, otp_ready;
  logic [OtpAddrWidth-1:0] otp_addr;
  logic [OtpWidth-1:0] otp_wdata, otp_rdata;
  logic otp_wren, otp_rvalid;

  // a couple of dummy connections to the OTP macro
  assign otp_valid = reg2hw.direct_access_wdata[1].qe | reg2hw.direct_access_cmd.write.qe;
  assign otp_wren = reg2hw.direct_access_wdata[1].qe;
  assign otp_addr = reg2hw.direct_access_address.q;
  assign otp_wdata = reg2hw.direct_access_wdata[1].q[OtpWidth - 1:0];

  assign otp_init_req = 1'b1;

  prim_otp #(
      .Width(OtpWidth),
      .Depth(OtpDepth),
      .ErrWidth(OtpErrWidth)
  ) i_prim_otp (
      .clk_i,
      .rst_ni,
      // Test inerface
      .test_tl_i  (tl_win_h2d[1]),
      .test_tl_o  (tl_win_d2h[1]),
      // Init and error signals
      .init_req_i (otp_init_req),
      .init_done_o(otp_init_done),
      .err_valid_o(otp_err_valid),
      .err_code_o (otp_err_code),
      // Read / Write command interface
      .ready_o    (otp_ready),
      .valid_i    (otp_valid),
      .addr_i     (otp_addr),
      .wdata_i    (otp_wdata),
      .wren_i     (otp_wren),
      // Read data out
      .rdata_o    (otp_rdata),
      .rvalid_o   (otp_rvalid)
  );

  ////////////////////
  // OTP Ctrl Logic //
  ////////////////////

  logic [31:0] gate_gen_out;
  logic gate_gen_out_valid;

  // gate generator with dummy connection to regfile
  prim_gate_gen #(
      .NumGates(30000)
  ) i_prim_gate_gen (
      .clk_i,
      .rst_ni,
      .data_i (reg2hw.direct_access_wdata[0].q),
      .valid_i(reg2hw.direct_access_wdata[0].qe),
      .data_o (gate_gen_out),
      .valid_o(gate_gen_out_valid)
  );

  /////////////////////
  // PRESENT ENC/DEC //
  /////////////////////

  logic [63:0] otp_scrambler_out;
  logic otp_scrambler_out_valid;

  otp_ctrl_scrmbl i_otp_ctrl_scrmbl (
      .clk_i,
      .rst_ni,
      .data_i ({reg2hw.direct_access_wdata[1].q, reg2hw.direct_access_wdata[0].q}),
      .cmd_i  (otp_scrmbl_cmd_e'(reg2hw.direct_access_wdata[1].q[2:0])),
      .valid_i(reg2hw.direct_access_wdata[1].qe),
      .ready_o(),
      .data_o (otp_scrambler_out),
      .valid_o(otp_scrambler_out_valid)
  );

  ///////////////////////////////////
  // Dummy Connections and Tie Off //
  ///////////////////////////////////

  always_comb begin : p_tie_off_or_connect
    // tie off
    hw2reg.status = '0;
    hw2reg.err_code = '0;
    hw2reg.direct_access_rdata = '0;
    hw2reg.lc_state = '0;
    hw2reg.id_state = '0;
    hw2reg.test_xxx_cnt = '0;
    hw2reg.transition_cnt = '0;
    hw2reg.secret_integrity_digest = '0;
    hw2reg.hw_cfg_lock = '0;
    hw2reg.hw_cfg = '0;
    hw2reg.hw_cfg_integrity_digest = '0;
    hw2reg.sw_cfg_integrity_digest = '0;

    // TODO: initialization should only performed once after reset. subsequent
    // init requests should just be immediately ack'ed without performing the complete
    // OTP boot sequence.
    pwr_otp_init_rsp_o = '0;
    otp_pwr_state_o = '0;
    lc_otp_program_rsp_o = '0;
    otp_lc_data_o = '0;
    otp_keymgr_key_o = '0;
    otp_flash_key_o = '0;

    // dummy connections
    {hw2reg.direct_access_rdata[0].d, hw2reg.direct_access_rdata[1].d} = otp_scrambler_out ^ {
      gate_gen_out, gate_gen_out
    };
    hw2reg.direct_access_rdata[0].de = gate_gen_out_valid ^ gate_gen_out_valid;
    hw2reg.direct_access_rdata[1].de = gate_gen_out_valid ^ gate_gen_out_valid;
    hw2reg.lc_state[0] = otp_rdata ^ {8{otp_rvalid}};
  end


endmodule : otp_ctrl
