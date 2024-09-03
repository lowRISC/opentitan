// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon top-level wrapper

module ascon
  import ascon_reg_pkg::*;
  import ascon_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,
  input rst_ni,
  input rst_shadowed_ni,

  // Idle indicator for clock manager
  output prim_mubi_pkg::mubi4_t idle_o,

   // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Entropy distribution network (EDN) interface
  input  logic              clk_edn_i,
  input  logic              rst_edn_ni,
  output edn_pkg::edn_req_t edn_o,
  input  edn_pkg::edn_rsp_t edn_i,

  // Key manager (keymgr) key sideload interface
  input  keymgr_pkg::hw_key_req_t keymgr_key_i,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o
);

  localparam int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH;

  // Signals
  ascon_reg2hw_t reg2hw;
  ascon_hw2reg_t hw2reg;

  logic [EntropyWidth-1:0] edn_data;
  logic                    edn_req;
  logic                    edn_ack;

  logic [NumAlerts-1:0] alert;

  logic ascon_fatal_alert;
  logic ascon_recov_alert;
  logic intg_err_alert;
  logic shadowed_storage_err;
  logic shadowed_update_err;

  ascon_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i,
    .tl_o,
    .reg2hw (reg2hw),
    .hw2reg (hw2reg),
    .intg_err_o(intg_err_alert),
    .shadowed_storage_err_o(shadowed_storage_err),
    .shadowed_update_err_o (shadowed_update_err)
  );

  ascon_core ascon_core (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .lc_escalate_en_i(lc_escalate_en_i),

    .alert_recov_o(ascon_recov_alert),
    .alert_fatal_o(ascon_fatal_alert),

    .error_recov_i(shadowed_update_err),
    .error_fatal_i(alert[1]),

    .keymgr_key_i,

    .reg2hw(reg2hw),
    .hw2reg(hw2reg),
    .idle_o(idle_o)
  );

  // Synchronize EDN interface
  prim_sync_reqack_data #(
    .Width(EntropyWidth),
    .DataSrc2Dst(1'b0),
    .DataReg(1'b0)
  ) u_prim_sync_reqack_data (
    .clk_src_i  ( clk_i         ),
    .rst_src_ni ( rst_ni        ),
    .clk_dst_i  ( clk_edn_i     ),
    .rst_dst_ni ( rst_edn_ni    ),
    .req_chk_i  ( 1'b1          ),
    .src_req_i  ( edn_req       ),
    .src_ack_o  ( edn_ack       ),
    .dst_req_o  ( edn_o.edn_req ),
    .dst_ack_i  ( edn_i.edn_ack ),
    .data_i     ( edn_i.edn_bus ),
    .data_o     ( edn_data      )
  );
  // We don't track whether the entropy is pre-FIPS or not inside Ascon.
  logic                      unused_edn_fips;
  assign unused_edn_fips = edn_i.edn_fips;

  // TODO
  logic   [EntropyWidth-1:0] unused_edn_data;
  logic                      unused_edn_ack;
  assign unused_edn_data = edn_data;
  assign edn_req = 1'b0;
  assign unused_edn_ack = edn_ack;


  // Alerts
  assign alert[1] = ascon_fatal_alert | intg_err_alert |shadowed_storage_err;
  assign alert[0] = ascon_recov_alert | shadowed_update_err;

  logic [NumAlerts-1:0] alert_test;
  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_ctrl_update_err.q &
    reg2hw.alert_test.recov_ctrl_update_err.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

endmodule
