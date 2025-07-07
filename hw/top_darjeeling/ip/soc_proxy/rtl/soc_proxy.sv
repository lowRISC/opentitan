// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SoC Proxy

`include "prim_assert.sv"

module soc_proxy
  import soc_proxy_reg_pkg::*;
  import soc_proxy_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Number of cycles a differential skew is tolerated on the alert signal
  parameter int unsigned AlertSkewCycles = 1
) (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic clk_aon_i,
  input  logic rst_por_ni,

  input  tlul_pkg::tl_h2d_t core_tl_i,
  output tlul_pkg::tl_d2h_t core_tl_o,

  input  tlul_pkg::tl_h2d_t ctn_tl_i,
  output tlul_pkg::tl_d2h_t ctn_tl_o,

  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  output logic wkup_external_req_o,

  output logic rst_req_external_o,

  // Integrator bits used for custom BAT
  input logic [3:0] integrator_id_i,

  input        [NumSocGpio-1:0] cio_soc_gpi_i,
  output logic [NumSocGpio-1:0] cio_soc_gpo_o,
  output logic [NumSocGpio-1:0] cio_soc_gpo_en_o,

  input  logic       i2c_lsio_trigger_i,
  input  logic       spi_host_lsio_trigger_i,
  input  logic       uart_lsio_trigger_i,
  input  logic [7:0] soc_lsio_trigger_i,
  output dma_pkg::lsio_trigger_t dma_lsio_trigger_o,

  // Incoming TL ports get muxed
  input  tlul_pkg::tl_h2d_t dma_tl_h2d_i,
  output tlul_pkg::tl_d2h_t dma_tl_d2h_o,
  input  tlul_pkg::tl_h2d_t misc_tl_h2d_i,
  output tlul_pkg::tl_d2h_t misc_tl_d2h_o,

  output tlul_pkg::tl_h2d_t ctn_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t ctn_tl_d2h_i,

  input  logic soc_wkup_async_i,

  input  logic soc_rst_req_async_i,

  output logic [NumSocGpio-1:0] soc_gpi_async_o,
  input  logic [NumSocGpio-1:0] soc_gpo_async_i
);
  localparam int unsigned TLUL_HOST_CNT = 3;

  // TLUL egress port muxing. First stage all incoming TLUL ports and them mux them
  tlul_pkg::tl_h2d_t host_tl_h2d[TLUL_HOST_CNT];
  tlul_pkg::tl_d2h_t host_tl_d2h[TLUL_HOST_CNT];

  assign host_tl_h2d [0] = ctn_tl_i;
  assign ctn_tl_o        = host_tl_d2h[0];

  assign host_tl_h2d [1] = dma_tl_h2d_i;
  assign dma_tl_d2h_o    = host_tl_d2h[1];

  assign host_tl_h2d [2] = misc_tl_h2d_i;
  assign misc_tl_d2h_o   = host_tl_d2h[2];

  tlul_pkg::tl_h2d_t muxed_host_tl_h2d;
  tlul_pkg::tl_d2h_t muxed_host_tl_d2h;

  // Add a MUX with a pipeline stage to shorten path through AC ranges
  tlul_socket_m1 #(
    .M         ( TLUL_HOST_CNT         ),
    .HReqPass  ( {TLUL_HOST_CNT{1'b1}} ),
    .HRspPass  ( {TLUL_HOST_CNT{1'b1}} ),
    .HReqDepth ( {TLUL_HOST_CNT{4'd2}} ),
    .HRspDepth ( {TLUL_HOST_CNT{4'd2}} ),
    .DReqPass  ( 0                     ),
    .DRspPass  ( 0                     ),
    .DReqDepth ( 4'd4                  ),
    .DRspDepth ( 4'd4                  )
  ) u_ctn_egress_mux (
    .clk_i  ( clk_i             ),
    .rst_ni ( rst_ni            ),
    .tl_h_i ( host_tl_h2d       ),
    .tl_h_o ( host_tl_d2h       ),
    .tl_d_o ( muxed_host_tl_h2d ),
    .tl_d_i ( muxed_host_tl_d2h )
  );

  // Perform the base address translation before exiting to the AC Ranges
  bat u_bat (
    .tl_in_h2d_i     ( muxed_host_tl_h2d ),
    .tl_in_d2h_o     ( muxed_host_tl_d2h ),
    .integrator_id_i ( integrator_id_i   ),
    .tl_out_h2d_o    ( ctn_tl_h2d_o      ),
    .tl_out_d2h_i    ( ctn_tl_d2h_i      )
  );

  // GPI/O signal feed through.
  assign soc_gpi_async_o  = cio_soc_gpi_i;
  assign cio_soc_gpo_en_o = {NumSocGpio{1'b1}};
  assign cio_soc_gpo_o    = soc_gpo_async_i;

  // Register node
  soc_proxy_core_reg2hw_t reg2hw;
  logic reg_top_intg_err;
  soc_proxy_core_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (core_tl_i),
    .tl_o       (core_tl_o),
    .reg2hw,
    .intg_err_o (reg_top_intg_err)
  );

  // Aggregate integrity alerts
  logic intg_err;
  assign intg_err = reg_top_intg_err;

  // Alert test
  logic [NumAlerts-1:0] alert_test;
  assign alert_test[AlertFatalAlertIntgIdx] = reg2hw.alert_test.q &
                                              reg2hw.alert_test.qe;


  // Alert sender for integrity alerts
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[AlertFatalAlertIntgIdx]),
    .SkewCycles(AlertSkewCycles),
    .IsFatal(1)
  ) u_prim_fatal_alert_intg_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i(alert_test[AlertFatalAlertIntgIdx]),
    .alert_req_i(intg_err),
    .alert_ack_o(),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[AlertFatalAlertIntgIdx]),
    .alert_tx_o(alert_tx_o[AlertFatalAlertIntgIdx])
  );

  // Synchronize external wakeup request
  prim_flop_2sync #(
    .Width(1)
  ) u_prim_flop_2sync_soc_wkup (
    .clk_i  (clk_aon_i),
    .rst_ni (rst_por_ni),
    .d_i    (soc_wkup_async_i),
    .q_o    (wkup_external_req_o)
  );

  // Synchronize reset request onto AON domain and filter out potential glitches
  prim_filter #(
    .AsyncOn(1'b1),
    .Cycles(4)
  ) u_prim_filter_soc_rst_req (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_por_ni),
    .enable_i (1'b1),
    .filter_i (soc_rst_req_async_i),
    .filter_o (rst_req_external_o)
  );

  // CDC sync of LSIO trigger signals between the peripheral and the high-speed clock domain
  logic uart_lsio_trigger_sync, spi_host_lsio_trigger_sync, i2c_lsio_trigger_sync;

  prim_flop_2sync #(
    .Width(1)
  ) u_uart_lsio_trigger_sync (
    .clk_i,
    .rst_ni,
    .d_i      (uart_lsio_trigger_i),
    .q_o      (uart_lsio_trigger_sync)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_spi_host_lsio_trigger_sync (
    .clk_i,
    .rst_ni,
    .d_i      (spi_host_lsio_trigger_i),
    .q_o      (spi_host_lsio_trigger_sync)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_i2c_lsio_trigger_sync (
    .clk_i,
    .rst_ni,
    .d_i    (i2c_lsio_trigger_i),
    .q_o    (i2c_lsio_trigger_sync)
  );

  // Collate LSIO trigger inputs into signal for DMA
  assign dma_lsio_trigger_o = {
    soc_lsio_trigger_i,
    uart_lsio_trigger_sync,
    spi_host_lsio_trigger_sync,
    i2c_lsio_trigger_sync
  };

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(DmaLsioTriggerKnown_A, dma_lsio_trigger_o)
  `ASSERT_KNOWN(CoreTlDValidKnownO_A, core_tl_o.d_valid)
  `ASSERT_KNOWN(CoreTlAReadyKnownO_A, core_tl_o.a_ready)

  // Assertions
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A,
                                                 u_reg,
                                                 alert_tx_o[AlertFatalAlertIntgIdx])

endmodule
