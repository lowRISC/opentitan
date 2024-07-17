// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// SoC Proxy

`include "prim_assert.sv"

module soc_proxy
  import soc_proxy_reg_pkg::*;
  import soc_proxy_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
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

  output logic [NumExternalIrqs-1:0] intr_external_o,

  output logic wkup_internal_req_o,
  output logic wkup_external_req_o,

  output logic rst_req_external_o,

  input        [NumSocGpio-1:0] cio_soc_gpi_i,
  output logic [NumSocGpio-1:0] cio_soc_gpo_o,
  output logic [NumSocGpio-1:0] cio_soc_gpo_en_o,

  input  logic       i2c_lsio_trigger_i,
  input  logic       spi_host_lsio_trigger_i,
  input  logic       spi_device_lsio_trigger_i,
  input  logic       uart_lsio_trigger_i,
  input  logic [6:0] soc_lsio_trigger_i,
  output dma_pkg::lsio_trigger_t dma_lsio_trigger_o,

  output tlul_pkg::tl_h2d_t ctn_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t ctn_tl_d2h_i,

  input  soc_alert_req_t [NumFatalExternalAlerts-1:0] soc_fatal_alert_i,
  output soc_alert_rsp_t [NumFatalExternalAlerts-1:0] soc_fatal_alert_o,
  input  soc_alert_req_t [NumRecovExternalAlerts-1:0] soc_recov_alert_i,
  output soc_alert_rsp_t [NumRecovExternalAlerts-1:0] soc_recov_alert_o,

  input  logic soc_wkup_async_i,

  input  logic soc_rst_req_async_i,

  output logic [NumSocGpio-1:0] soc_gpi_async_o,
  input  logic [NumSocGpio-1:0] soc_gpo_async_i,

  input  logic [NumExternalIrqs-1:0] soc_intr_async_i
);

  // Feed CTN TL-UL ports through.
  assign ctn_tl_h2d_o = ctn_tl_i;
  assign ctn_tl_o = ctn_tl_d2h_i;

  // GPI/O signal feed through.
  assign soc_gpi_async_o  = cio_soc_gpi_i;
  assign cio_soc_gpo_en_o = {NumSocGpio{1'b1}};
  assign cio_soc_gpo_o    = soc_gpo_async_i;

  // Register node
  soc_proxy_core_reg2hw_t reg2hw;
  soc_proxy_core_hw2reg_t hw2reg;
  logic reg_top_intg_err;
  soc_proxy_core_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i       (core_tl_i),
    .tl_o       (core_tl_o),
    .reg2hw,
    .hw2reg,
    .intg_err_o (reg_top_intg_err),
    .devmode_i  (1'b1)
  );

  // Alert test
  logic [NumAlerts-1:0] alert_test;
  assign alert_test[FatalAlertIntg] = reg2hw.alert_test.fatal_alert_intg.qe &
                                      reg2hw.alert_test.fatal_alert_intg.q;
  assign alert_test[FatalAlertExternal0] = reg2hw.alert_test.fatal_alert_external_0.qe &
                                           reg2hw.alert_test.fatal_alert_external_0.q;
  assign alert_test[FatalAlertExternal1] = reg2hw.alert_test.fatal_alert_external_1.qe &
                                           reg2hw.alert_test.fatal_alert_external_1.q;
  assign alert_test[FatalAlertExternal2] = reg2hw.alert_test.fatal_alert_external_2.qe &
                                           reg2hw.alert_test.fatal_alert_external_2.q;
  assign alert_test[FatalAlertExternal3] = reg2hw.alert_test.fatal_alert_external_3.qe &
                                           reg2hw.alert_test.fatal_alert_external_3.q;
  assign alert_test[FatalAlertExternal4] = reg2hw.alert_test.fatal_alert_external_4.qe &
                                           reg2hw.alert_test.fatal_alert_external_4.q;
  assign alert_test[FatalAlertExternal5] = reg2hw.alert_test.fatal_alert_external_5.qe &
                                           reg2hw.alert_test.fatal_alert_external_5.q;
  assign alert_test[FatalAlertExternal6] = reg2hw.alert_test.fatal_alert_external_6.qe &
                                           reg2hw.alert_test.fatal_alert_external_6.q;
  assign alert_test[FatalAlertExternal7] = reg2hw.alert_test.fatal_alert_external_7.qe &
                                           reg2hw.alert_test.fatal_alert_external_7.q;
  assign alert_test[FatalAlertExternal8] = reg2hw.alert_test.fatal_alert_external_8.qe &
                                           reg2hw.alert_test.fatal_alert_external_8.q;
  assign alert_test[FatalAlertExternal9] = reg2hw.alert_test.fatal_alert_external_9.qe &
                                           reg2hw.alert_test.fatal_alert_external_9.q;
  assign alert_test[FatalAlertExternal10] = reg2hw.alert_test.fatal_alert_external_10.qe &
                                            reg2hw.alert_test.fatal_alert_external_10.q;
  assign alert_test[FatalAlertExternal11] = reg2hw.alert_test.fatal_alert_external_11.qe &
                                            reg2hw.alert_test.fatal_alert_external_11.q;
  assign alert_test[FatalAlertExternal12] = reg2hw.alert_test.fatal_alert_external_12.qe &
                                            reg2hw.alert_test.fatal_alert_external_12.q;
  assign alert_test[FatalAlertExternal13] = reg2hw.alert_test.fatal_alert_external_13.qe &
                                            reg2hw.alert_test.fatal_alert_external_13.q;
  assign alert_test[FatalAlertExternal14] = reg2hw.alert_test.fatal_alert_external_14.qe &
                                            reg2hw.alert_test.fatal_alert_external_14.q;
  assign alert_test[FatalAlertExternal15] = reg2hw.alert_test.fatal_alert_external_15.qe &
                                            reg2hw.alert_test.fatal_alert_external_15.q;
  assign alert_test[FatalAlertExternal16] = reg2hw.alert_test.fatal_alert_external_16.qe &
                                            reg2hw.alert_test.fatal_alert_external_16.q;
  assign alert_test[FatalAlertExternal17] = reg2hw.alert_test.fatal_alert_external_17.qe &
                                            reg2hw.alert_test.fatal_alert_external_17.q;
  assign alert_test[FatalAlertExternal18] = reg2hw.alert_test.fatal_alert_external_18.qe &
                                            reg2hw.alert_test.fatal_alert_external_18.q;
  assign alert_test[FatalAlertExternal19] = reg2hw.alert_test.fatal_alert_external_19.qe &
                                            reg2hw.alert_test.fatal_alert_external_19.q;
  assign alert_test[FatalAlertExternal20] = reg2hw.alert_test.fatal_alert_external_20.qe &
                                            reg2hw.alert_test.fatal_alert_external_20.q;
  assign alert_test[FatalAlertExternal21] = reg2hw.alert_test.fatal_alert_external_21.qe &
                                            reg2hw.alert_test.fatal_alert_external_21.q;
  assign alert_test[FatalAlertExternal22] = reg2hw.alert_test.fatal_alert_external_22.qe &
                                            reg2hw.alert_test.fatal_alert_external_22.q;
  assign alert_test[FatalAlertExternal23] = reg2hw.alert_test.fatal_alert_external_23.qe &
                                            reg2hw.alert_test.fatal_alert_external_23.q;

  assign alert_test[RecovAlertExternal0] = reg2hw.alert_test.recov_alert_external_0.qe &
                                           reg2hw.alert_test.recov_alert_external_0.q;
  assign alert_test[RecovAlertExternal1] = reg2hw.alert_test.recov_alert_external_1.qe &
                                           reg2hw.alert_test.recov_alert_external_1.q;
  assign alert_test[RecovAlertExternal2] = reg2hw.alert_test.recov_alert_external_2.qe &
                                           reg2hw.alert_test.recov_alert_external_2.q;
  assign alert_test[RecovAlertExternal3] = reg2hw.alert_test.recov_alert_external_3.qe &
                                           reg2hw.alert_test.recov_alert_external_3.q;

  // Handle fatal external alert requests
  logic [NumFatalExternalAlerts-1:0] fatal_alert_external, fatal_alert_external_async;
  logic [NumFatalExternalAlerts-1:0] soc_fatal_alert_p, soc_fatal_alert_n;
  logic [NumFatalExternalAlerts-1:0] soc_fatal_alert_ack_p_d, soc_fatal_alert_ack_n_d;

  // Acknowledge alert based on request.
  // Ensure that Ack has always a valid encoding and we swallow a staggered _p/_n signal
  always_comb begin
    for(int i = 0; i < NumFatalExternalAlerts; i++) begin
      // Acknowledge alert based on request.
      // Ensure that Ack has always a valid encoding and we swallow a staggered _p/_n signal
      if (soc_fatal_alert_p[i] ^ soc_fatal_alert_n[i]) begin
        soc_fatal_alert_ack_p_d[i] = soc_fatal_alert_p[i];
        soc_fatal_alert_ack_n_d[i] = soc_fatal_alert_n[i];
      end else begin
        soc_fatal_alert_ack_p_d[i] = soc_fatal_alert_o[i].ack_p;
        soc_fatal_alert_ack_n_d[i] = soc_fatal_alert_o[i].ack_n;
      end
    end
  end

  for (genvar i = 0; i < NumFatalExternalAlerts; i++) begin : gen_fatal_alert_handling
    // Treat any positive value on `alert_p` and any negative value on `alert_n` as alert.
    // Combinationally determine the alert on the input signals to generater an asynchronous
    // wakeup.
    assign fatal_alert_external_async[i] = soc_fatal_alert_p[i] | ~soc_fatal_alert_n[i];

    // Synchronize external differentially encoded alert to internal clk domain
    prim_flop_2sync #(
      .Width(1),
      .ResetValue(1'b0)
    ) u_prim_flop_2sync_fatal_alert_p (
      .clk_i,
      .rst_ni,
      .d_i    (soc_fatal_alert_i[i].alert_p),
      .q_o    (soc_fatal_alert_p[i])
    );
    prim_flop_2sync #(
      .Width(1),
      .ResetValue(1'b1)
    ) u_prim_flop_2sync_fatal_alert_n (
      .clk_i,
      .rst_ni,
      .d_i    (soc_fatal_alert_i[i].alert_n),
      .q_o    (soc_fatal_alert_n[i])
    );
    // Treat any positive value on `alert_p` and any negative value on `alert_n` as alert.
    assign fatal_alert_external[i] = soc_fatal_alert_p[i] | ~soc_fatal_alert_n[i];

    prim_flop #(
      .Width(1),
      .ResetValue(1'b0)
    ) u_prim_flop_fatal_ack_p (
      .clk_i,
      .rst_ni,
      .d_i    (soc_fatal_alert_ack_p_d[i]),
      .q_o    (soc_fatal_alert_o[i].ack_p)
    );

    prim_flop #(
      .Width(1),
      .ResetValue(1'b1)
    ) u_prim_flop_fatal_ack_n (
      .clk_i,
      .rst_ni,
      .d_i    (soc_fatal_alert_ack_n_d[i]),
      .q_o    (soc_fatal_alert_o[i].ack_n)
    );
  end

  // Handle recoverable external alert requests
  logic [NumRecovExternalAlerts-1:0] recov_alert_external, recov_alert_external_async;
  logic [NumRecovExternalAlerts-1:0] soc_recov_alert_p, soc_recov_alert_n;
  logic [NumRecovExternalAlerts-1:0] soc_recov_alert_ack_p_d, soc_recov_alert_ack_n_d;

  // Acknowledge alert based on request.
  // Ensure that Ack has always a valid encoding and we swallow a staggered _p/_n signal
  always_comb begin
    for(int i = 0; i < NumRecovExternalAlerts; i++) begin
      if (soc_recov_alert_p[i] ^ soc_recov_alert_n[i]) begin
        soc_recov_alert_ack_p_d[i] = soc_recov_alert_p[i];
        soc_recov_alert_ack_n_d[i] = soc_recov_alert_n[i];
      end else begin
        soc_recov_alert_ack_p_d[i] = soc_recov_alert_o[i].ack_p;
        soc_recov_alert_ack_n_d[i] = soc_recov_alert_o[i].ack_n;
      end
    end
  end

  for (genvar i = 0; i < NumRecovExternalAlerts; i++) begin : gen_recov_alert_handling
    // Treat any positive value on `alert_p` and any negative value on `alert_n` as alert.
    // Combinationally determine the alert on the input signals to generater an asynchronous
    // wakeup.
    assign recov_alert_external_async[i] =  soc_recov_alert_i[i].alert_p |
                                           ~soc_recov_alert_i[i].alert_n;

    // Synchronize external differentially encoded alert to internal clk domain
    prim_flop_2sync #(
      .Width(1),
      .ResetValue(1'b0)
    ) u_prim_flop_2sync_recov_alert_p (
      .clk_i,
      .rst_ni,
      .d_i    (soc_recov_alert_i[i].alert_p),
      .q_o    (soc_recov_alert_p[i])
    );
    prim_flop_2sync #(
      .Width(1),
      .ResetValue(1'b1)
    ) u_prim_flop_2sync_recov_alert_n (
      .clk_i,
      .rst_ni,
      .d_i    (soc_recov_alert_i[i].alert_n),
      .q_o    (soc_recov_alert_n[i])
    );
    // Treat any positive value on `alert_p` and any negative value on `alert_n` as alert.
    assign recov_alert_external[i] = soc_recov_alert_p[i] | ~soc_recov_alert_n[i];

    prim_flop #(
      .Width(1),
      .ResetValue(1'b0)
    ) u_prim_flop_recov_ack_p (
      .clk_i,
      .rst_ni,
      .d_i    (soc_recov_alert_ack_p_d[i]),
      .q_o    (soc_recov_alert_o[i].ack_p)
    );

    prim_flop #(
      .Width(1),
      .ResetValue(1'b1)
    ) u_prim_flop_recov_ack_n (
      .clk_i,
      .rst_ni,
      .d_i    (soc_recov_alert_ack_n_d[i]),
      .q_o    (soc_recov_alert_o[i].ack_n)
    );
  end

  // Aggregate integrity alerts
  logic intg_err;
  assign intg_err = reg_top_intg_err;

  // Alert sender for integrity alerts
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[FatalAlertIntg]),
    .IsFatal(1)
  ) u_prim_fatal_alert_intg_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i(alert_test[FatalAlertIntg]),
    .alert_req_i(intg_err),
    .alert_ack_o(),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[FatalAlertIntg]),
    .alert_tx_o(alert_tx_o[FatalAlertIntg])
  );

  // Alert senders for fatal external alerts
  for (genvar i = 0; i < NumFatalExternalAlerts; i++) begin : gen_fatal_alert_sender
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[FatalAlertExternal0 + i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i(alert_test[FatalAlertExternal0 + i]),
      .alert_req_i(fatal_alert_external[i]),
      .alert_ack_o(),
      .alert_state_o(),
      .alert_rx_i(alert_rx_i[FatalAlertExternal0 + i]),
      .alert_tx_o(alert_tx_o[FatalAlertExternal0 + i])
    );
  end

  // Alert senders for recoverable external alerts
  for (genvar i = 0; i < NumRecovExternalAlerts; i++) begin : gen_recov_alert_sender
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[RecovAlertExternal0 + i]),
      .IsFatal(1'b0)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i(alert_test[RecovAlertExternal0 + i]),
      .alert_req_i(recov_alert_external[i]),
      .alert_ack_o(),
      .alert_state_o(),
      .alert_rx_i(alert_rx_i[RecovAlertExternal0 + i]),
      .alert_tx_o(alert_tx_o[RecovAlertExternal0 + i])
    );
  end

  // Synchronize external interrupt signals
  logic [NumExternalIrqs-1:0] soc_intr;
  for (genvar i = 0; i < NumExternalIrqs; i++) begin : gen_sync_external_irqs
    prim_flop_2sync #(
      .Width(1)
    ) u_prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(soc_intr_async_i[i]),
      .q_o(soc_intr[i])
    );
  end

  // Handle external interrupts
  prim_intr_hw #(
    .Width(NumExternalIrqs)
  ) u_prim_intr_hw (
    .clk_i,
    .rst_ni,
    .event_intr_i           (soc_intr),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.d),
    .intr_o                 (intr_external_o)
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

  // Generate internal wakeup signal combinatorially from asynchronous signals
  logic async_wkup;
  assign async_wkup = |{fatal_alert_external_async, recov_alert_external_async, soc_intr_async_i};

  // Synchronize wakeup signal onto AON domain and filter out potential glitches
  prim_filter #(
    .AsyncOn(1'b1),
    .Cycles(3)
  ) u_prim_filter_wkup (
    .clk_i    (clk_aon_i),
    .rst_ni   (rst_por_ni),
    .enable_i (1'b1),
    .filter_i (async_wkup),
    .filter_o (wkup_internal_req_o)
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
  logic uart_lsio_trigger_sync, spi_host_lsio_trigger_sync, spi_device_lsio_trigger_sync,
        i2c_lsio_trigger_sync;

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
  ) u_spi_device_lsio_trigger_sync (
    .clk_i,
    .rst_ni,
    .d_i      (spi_device_lsio_trigger_i),
    .q_o      (spi_device_lsio_trigger_sync)
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
    spi_device_lsio_trigger_sync,
    uart_lsio_trigger_sync,
    spi_host_lsio_trigger_sync,
    i2c_lsio_trigger_sync
  };

  // Assertions
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A,
                                                 u_reg,
                                                 alert_tx_o[FatalAlertIntg])

  // Assert that there's one index for each alert defined in the Hjson.
  `ASSERT_INIT(AlertSourcesComplete_A, NumAlertSources == NumAlerts)

  // Assert that the number of internal and external alerts sum up to the total number of alerts.
  `ASSERT_INIT(AlertNumsSumCorrect_A, NumInternalAlerts + NumExternalAlerts == NumAlertSources)

endmodule
