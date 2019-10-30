// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Alert handler top.
//
// Note that the alert_pkg, the regfile and alert_handler_reg_wrap
// have to be generated using the reg_alert_handler.py script.
//

module alert_handler (
  input                                    clk_i,
  input                                    rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                tl_i,
  output tlul_pkg::tl_d2h_t                tl_o,
  // Interrupt Requests
  output logic [alert_pkg::N_CLASSES-1:0]  irq_o,
  // State information for HW crashdump
  output alert_pkg::alert_crashdump_t      crashdump_o,
  // Entropy Input from TRNG
  input                                    entropy_i,
  // Alert Sources
  input        [alert_pkg::NAlerts-1:0]    alert_pi,
  input        [alert_pkg::NAlerts-1:0]    alert_ni,
  output logic [alert_pkg::NAlerts-1:0]    ack_po,
  output logic [alert_pkg::NAlerts-1:0]    ack_no,
  output logic [alert_pkg::NAlerts-1:0]    ping_po,
  output logic [alert_pkg::NAlerts-1:0]    ping_no,
  // Escalation outputs
  output logic [alert_pkg::N_ESC_SEV-1:0]  esc_po,
  output logic [alert_pkg::N_ESC_SEV-1:0]  esc_no,
  input        [alert_pkg::N_ESC_SEV-1:0]  resp_pi,
  input        [alert_pkg::N_ESC_SEV-1:0]  resp_ni
);

  //////////////////////////////////////////////////////
  // Regfile Breakout and Mapping
  //////////////////////////////////////////////////////

  alert_pkg::hw2reg_wrap_t hw2reg_wrap;
  alert_pkg::reg2hw_wrap_t reg2hw_wrap;

  alert_handler_reg_wrap i_reg_wrap (
    .clk_i       ,
    .rst_ni      ,
    .tl_i        ,
    .tl_o        ,
    .irq_o       ,
    .crashdump_o ,
    .hw2reg_wrap ,
    .reg2hw_wrap
  );

  //////////////////////////////////////////////////////
  // Ping Timer
  //////////////////////////////////////////////////////

  logic [alert_pkg::N_LOC_ALERT-1:0] loc_alert_trig;

  logic [alert_pkg::NAlerts-1:0]   alert_ping_en;
  logic [alert_pkg::NAlerts-1:0]   alert_ping_ok;
  logic [alert_pkg::N_ESC_SEV-1:0] esc_ping_en;
  logic [alert_pkg::N_ESC_SEV-1:0] esc_ping_ok;

  alert_handler_ping_timer i_ping_timer (
    .clk_i,
    .rst_ni,
    .entropy_i,
    // we enable ping testing as soon as the config
    // regs have been locked
    .en_i               ( reg2hw_wrap.config_locked     ),
    .alert_en_i         ( reg2hw_wrap.alert_en          ),
    .ping_timeout_cyc_i ( reg2hw_wrap.ping_timeout_cyc  ),
    .alert_ping_en_o    ( alert_ping_en                 ),
    .esc_ping_en_o      ( esc_ping_en                   ),
    .alert_ping_ok_i    ( alert_ping_ok                 ),
    .esc_ping_ok_i      ( esc_ping_ok                   ),
    .alert_ping_fail_o  ( loc_alert_trig[0]             ),
    .esc_ping_fail_o    ( loc_alert_trig[1]             )
  );

  //////////////////////////////////////////////////////
  // Alert Receivers
  //////////////////////////////////////////////////////

  logic [alert_pkg::NAlerts-1:0] alert_integfail;
  logic [alert_pkg::NAlerts-1:0] alert_trig;

  // Target interrupt notification
  for (genvar k = 0 ; k < alert_pkg::NAlerts ; k++) begin : gen_alerts
    prim_alert_receiver #(
      .AsyncOn(alert_pkg::AsyncOn[k])
    ) i_alert_receiver (
      .clk_i                               ,
      .rst_ni                              ,
      .ping_en_i    ( alert_ping_en[k]    ),
      .ping_ok_o    ( alert_ping_ok[k]    ),
      .integ_fail_o ( alert_integfail[k]  ),
      .alert_o      ( alert_trig[k]       ),
      .ping_po      ( ping_po[k]          ),
      .ping_no      ( ping_no[k]          ),
      .ack_po       ( ack_po[k]           ),
      .ack_no       ( ack_no[k]           ),
      .alert_pi     ( alert_pi[k]         ),
      .alert_ni     ( alert_ni[k]         )
    );
  end

  assign loc_alert_trig[2] = |(reg2hw_wrap.alert_en & alert_integfail);

  //////////////////////////////////////////////////////
  // Set alert cause bits and classify
  //////////////////////////////////////////////////////

  alert_handler_class i_class (
    .alert_trig_i      ( alert_trig                  ),
    .loc_alert_trig_i  ( loc_alert_trig              ),
    .alert_en_i        ( reg2hw_wrap.alert_en        ),
    .loc_alert_en_i    ( reg2hw_wrap.loc_alert_en    ),
    .alert_class_i     ( reg2hw_wrap.alert_class     ),
    .loc_alert_class_i ( reg2hw_wrap.loc_alert_class ),
    .class_en_i        ( reg2hw_wrap.class_en        ),
    .alert_cause_o     ( hw2reg_wrap.alert_cause     ),
    .loc_alert_cause_o ( hw2reg_wrap.loc_alert_cause ),
    .class_trig_o      ( hw2reg_wrap.class_trig      )
  );

  //////////////////////////////////////////////////////
  // Escalation Handling of Classes
  //////////////////////////////////////////////////////

  logic [alert_pkg::N_CLASSES-1:0] class_accum_trig;
  logic [alert_pkg::N_CLASSES-1:0][alert_pkg::N_ESC_SEV-1:0] class_esc_sig_en;

  for (genvar k = 0; k < alert_pkg::N_CLASSES; k++) begin : gen_classes
    alert_handler_accu i_accu (
      .clk_i,
      .rst_ni,
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
      .timeout_en_i     ( irq_o[k]                         ),
      .accum_trig_i     ( class_accum_trig[k]              ),
      .timeout_cyc_i    ( reg2hw_wrap.class_timeout_cyc[k] ),
      .esc_en_i         ( reg2hw_wrap.class_esc_en[k]      ),
      .esc_map_i        ( reg2hw_wrap.class_esc_map[k]     ),
      .phase_cyc_i      ( reg2hw_wrap.class_phase_cyc[k]   ),
      .esc_trig_o       ( hw2reg_wrap.class_esc_trig[k]    ),
      .esc_cnt_o        ( hw2reg_wrap.class_esc_cnt[k]     ),
      .esc_state_o      ( hw2reg_wrap.class_esc_state[k]   ),
      .esc_sig_en_o     ( class_esc_sig_en[k]              )
    );
  end

  //////////////////////////////////////////////////////
  // Escalation Senders
  //////////////////////////////////////////////////////

  logic [alert_pkg::N_ESC_SEV-1:0] esc_sig_en;
  logic [alert_pkg::N_ESC_SEV-1:0] esc_integfail;
  logic [alert_pkg::N_ESC_SEV-1:0][alert_pkg::N_CLASSES-1:0] esc_sig_en_trsp;

  for (genvar k = 0; k < alert_pkg::N_ESC_SEV; k++) begin : gen_esc_sev
    for (genvar j = 0; j < alert_pkg::N_CLASSES; j++) begin : gen_transp
      assign esc_sig_en_trsp[k][j] = class_esc_sig_en[j][k];
    end

    assign esc_sig_en[k] = |esc_sig_en_trsp[k];

    prim_esc_sender i_esc_sender (
      .clk_i,
      .rst_ni,
      .ping_en_i    ( esc_ping_en[k]   ),
      .ping_ok_o    ( esc_ping_ok[k]   ),
      .integ_fail_o ( esc_integfail[k] ),
      .esc_en_i     ( esc_sig_en[k]    ),
      .resp_pi      ( resp_pi[k]       ),
      .resp_ni      ( resp_ni[k]       ),
      .esc_po       ( esc_po[k]        ),
      .esc_no       ( esc_no[k]        )
    );
  end

  assign loc_alert_trig[3] = |esc_integfail;

  //////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(TlKnownO_A, tl_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(IrqKnownO_A, irq_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(CrashdumpKnownO_A, crashdump_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(PingPKnownO_A, ping_po, clk_i, !rst_ni)
  `ASSERT_KNOWN(PingNKnownO_A, ping_no, clk_i, !rst_ni)
  `ASSERT_KNOWN(AckPKnownO_A, ack_po, clk_i, !rst_ni)
  `ASSERT_KNOWN(AckNKnownO_A, ack_no, clk_i, !rst_ni)
  `ASSERT_KNOWN(EscPKnownO_A, esc_po, clk_i, !rst_ni)
  `ASSERT_KNOWN(EscNKnownO_A, esc_no, clk_i, !rst_ni)

  // this restriction is due to specifics in the ping selection mechanism
  `ASSERT_INIT(CheckNAlerts,
      alert_pkg::NAlerts  < (256 - alert_pkg::N_CLASSES))
  `ASSERT_INIT(CheckEscCntDw,  alert_pkg::EscCntDw  <= 32)
  `ASSERT_INIT(CheckAccuCntDw, alert_pkg::AccuCntDw <= 32)
  `ASSERT_INIT(CheckNClasses,  alert_pkg::N_CLASSES <= 8)
  `ASSERT_INIT(CheckNEscSev,   alert_pkg::N_ESC_SEV <= 8)

endmodule
