// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Alert handler top.
//
// Note that the alert_pkg, the regfile and alert_handler_reg_wrap
// have to be generated using the reg_alert_handler.py script.
//

`include "prim_assert.sv"

module alert_handler
  import alert_pkg::*;
  import prim_alert_pkg::*;
  import prim_esc_pkg::*;
#(
  // Compile time random constants, to be overriden by topgen.
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault
) (
  input                           clk_i,
  input                           rst_ni,
  input                           clk_edn_i,
  input                           rst_edn_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t       tl_i,
  output tlul_pkg::tl_d2h_t       tl_o,
  // Interrupt Requests
  output logic                    intr_classa_o,
  output logic                    intr_classb_o,
  output logic                    intr_classc_o,
  output logic                    intr_classd_o,
  // State information for HW crashdump
  output alert_crashdump_t        crashdump_o,
  // Entropy Input
  output edn_pkg::edn_req_t       edn_o,
  input  edn_pkg::edn_rsp_t       edn_i,
  // Alert Sources
  input  alert_tx_t [NAlerts-1:0] alert_tx_i,
  output alert_rx_t [NAlerts-1:0] alert_rx_o,
  // Escalation outputs
  input  esc_rx_t [N_ESC_SEV-1:0] esc_rx_i,
  output esc_tx_t [N_ESC_SEV-1:0] esc_tx_o
);

  //////////////////////////////////
  // Regfile Breakout and Mapping //
  //////////////////////////////////

  logic [N_CLASSES-1:0] irq;
  hw2reg_wrap_t hw2reg_wrap;
  reg2hw_wrap_t reg2hw_wrap;

  // TODO: make this fully parametric at some point
  assign {intr_classd_o,
          intr_classc_o,
          intr_classb_o,
          intr_classa_o} = irq;

  alert_handler_reg_wrap i_reg_wrap (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .irq_o ( irq ),
    .crashdump_o,
    .hw2reg_wrap,
    .reg2hw_wrap
  );

  ////////////////
  // Ping Timer //
  ////////////////

  logic [N_LOC_ALERT-1:0] loc_alert_trig;

  logic [NAlerts-1:0]   alert_ping_req;
  logic [NAlerts-1:0]   alert_ping_ok;
  logic [N_ESC_SEV-1:0] esc_ping_req;
  logic [N_ESC_SEV-1:0] esc_ping_ok;

  logic entropy;

  // This module pings for entropy excessively at the moment,
  // but this will be addressed later using a refresh rate
  prim_edn_req #(
    .OutWidth(1)
  ) u_edn_req (
    .clk_i,
    .rst_ni,
    .req_i(1'b0),
    .ack_o(),
    .data_o(entropy),
    .fips_o(),
    .clk_edn_i,
    .rst_edn_ni,
    .edn_o(edn_o),
    .edn_i(edn_i)
  );

  alert_handler_ping_timer #(
    .RndCnstLfsrSeed(RndCnstLfsrSeed),
    .RndCnstLfsrPerm(RndCnstLfsrPerm)
  ) i_ping_timer (
    .clk_i,
    .rst_ni,
    .entropy_i(entropy),
    // we enable ping testing as soon as the config
    // regs have been locked
    .en_i               ( reg2hw_wrap.ping_enable      ),
    .alert_ping_en_i    ( reg2hw_wrap.alert_ping_en    ),
    .ping_timeout_cyc_i ( reg2hw_wrap.ping_timeout_cyc ),
    // this determines the range of the randomly generated
    // wait period between ping. maximum mask width is PING_CNT_DW.
    .wait_cyc_mask_i    ( PING_CNT_DW'(24'hFFFFFF)     ),
    .alert_ping_req_o   ( alert_ping_req               ),
    .esc_ping_req_o     ( esc_ping_req                 ),
    .alert_ping_ok_i    ( alert_ping_ok                ),
    .esc_ping_ok_i      ( esc_ping_ok                  ),
    .alert_ping_fail_o  ( loc_alert_trig[0]            ),
    .esc_ping_fail_o    ( loc_alert_trig[1]            )
  );

  /////////////////////
  // Alert Receivers //
  /////////////////////

  logic [NAlerts-1:0] alert_integfail;
  logic [NAlerts-1:0] alert_trig;

  // Target interrupt notification
  for (genvar k = 0 ; k < NAlerts ; k++) begin : gen_alerts
    prim_alert_receiver #(
      .AsyncOn(AsyncOn[k])
    ) i_alert_receiver (
      .clk_i                              ,
      .rst_ni                             ,
      .ping_req_i   ( alert_ping_req[k]   ),
      .ping_ok_o    ( alert_ping_ok[k]   ),
      .integ_fail_o ( alert_integfail[k] ),
      .alert_o      ( alert_trig[k]      ),
      .alert_rx_o   ( alert_rx_o[k]      ),
      .alert_tx_i   ( alert_tx_i[k]      )
    );
  end

  assign loc_alert_trig[2] = |(reg2hw_wrap.alert_en & alert_integfail);

  ///////////////////////////////////////
  // Set alert cause bits and classify //
  ///////////////////////////////////////

  alert_handler_class i_class (
    .alert_trig_i      ( alert_trig                  ),
    .loc_alert_trig_i  ( loc_alert_trig              ),
    .alert_en_i        ( reg2hw_wrap.alert_en        ),
    .loc_alert_en_i    ( reg2hw_wrap.loc_alert_en    ),
    .alert_class_i     ( reg2hw_wrap.alert_class     ),
    .loc_alert_class_i ( reg2hw_wrap.loc_alert_class ),
    .alert_cause_o     ( hw2reg_wrap.alert_cause     ),
    .loc_alert_cause_o ( hw2reg_wrap.loc_alert_cause ),
    .class_trig_o      ( hw2reg_wrap.class_trig      )
  );

  ////////////////////////////////////
  // Escalation Handling of Classes //
  ////////////////////////////////////

  logic [N_CLASSES-1:0] class_accum_trig;
  logic [N_CLASSES-1:0][N_ESC_SEV-1:0] class_esc_sig_req;

  for (genvar k = 0; k < N_CLASSES; k++) begin : gen_classes
    alert_handler_accu i_accu (
      .clk_i,
      .rst_ni,
      .class_en_i   ( reg2hw_wrap.class_en[k]           ),
      .clr_i        ( reg2hw_wrap.class_clr[k]          ),
      .class_trig_i ( hw2reg_wrap.class_trig[k]         ),
      .thresh_i     ( reg2hw_wrap.class_accum_thresh[k] ),
      .accu_cnt_o   ( hw2reg_wrap.class_accum_cnt[k]    ),
      .accu_trig_o  ( class_accum_trig[k]               )
    );

    alert_handler_esc_timer i_esc_timer (
      .clk_i,
      .rst_ni,
      .en_i             ( reg2hw_wrap.class_en[k]          ),
      // this clear does not apply to interrupts
      .clr_i            ( reg2hw_wrap.class_clr[k]         ),
      // an interrupt enables the timeout
      .timeout_en_i     ( irq[k]                           ),
      .accum_trig_i     ( class_accum_trig[k]              ),
      .timeout_cyc_i    ( reg2hw_wrap.class_timeout_cyc[k] ),
      .esc_en_i         ( reg2hw_wrap.class_esc_en[k]      ),
      .esc_map_i        ( reg2hw_wrap.class_esc_map[k]     ),
      .phase_cyc_i      ( reg2hw_wrap.class_phase_cyc[k]   ),
      .esc_trig_o       ( hw2reg_wrap.class_esc_trig[k]    ),
      .esc_cnt_o        ( hw2reg_wrap.class_esc_cnt[k]     ),
      .esc_state_o      ( hw2reg_wrap.class_esc_state[k]   ),
      .esc_sig_req_o    ( class_esc_sig_req[k]             )
    );
  end

  ////////////////////////
  // Escalation Senders //
  ////////////////////////

  logic [N_ESC_SEV-1:0] esc_sig_req;
  logic [N_ESC_SEV-1:0] esc_integfail;
  logic [N_ESC_SEV-1:0][N_CLASSES-1:0] esc_sig_req_trsp;

  for (genvar k = 0; k < N_ESC_SEV; k++) begin : gen_esc_sev
    for (genvar j = 0; j < N_CLASSES; j++) begin : gen_transp
      assign esc_sig_req_trsp[k][j] = class_esc_sig_req[j][k];
    end

    assign esc_sig_req[k] = |esc_sig_req_trsp[k];

    prim_esc_sender i_esc_sender (
      .clk_i,
      .rst_ni,
      .ping_req_i   ( esc_ping_req[k]  ),
      .ping_ok_o    ( esc_ping_ok[k]   ),
      .integ_fail_o ( esc_integfail[k] ),
      .esc_req_i    ( esc_sig_req[k]   ),
      .esc_rx_i     ( esc_rx_i[k]      ),
      .esc_tx_o     ( esc_tx_o[k]      )
    );
  end

  assign loc_alert_trig[3] = |esc_integfail;

  ////////////////
  // Assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(IrqAKnownO_A, intr_classa_o)
  `ASSERT_KNOWN(IrqBKnownO_A, intr_classb_o)
  `ASSERT_KNOWN(IrqCKnownO_A, intr_classc_o)
  `ASSERT_KNOWN(IrqDKnownO_A, intr_classd_o)
  `ASSERT_KNOWN(CrashdumpKnownO_A, crashdump_o)
  `ASSERT_KNOWN(AckPKnownO_A, alert_rx_o)
  `ASSERT_KNOWN(EscPKnownO_A, esc_tx_o)

  // this restriction is due to specifics in the ping selection mechanism
  `ASSERT_INIT(CheckNAlerts,   NAlerts  < (256 - N_CLASSES))
  `ASSERT_INIT(CheckEscCntDw,  EscCntDw  <= 32)
  `ASSERT_INIT(CheckAccuCntDw, AccuCntDw <= 32)
  `ASSERT_INIT(CheckNClasses,  N_CLASSES <= 8)
  `ASSERT_INIT(CheckNEscSev,   N_ESC_SEV <= 8)

endmodule
