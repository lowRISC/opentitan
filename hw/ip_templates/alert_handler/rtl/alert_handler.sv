// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Alert handler top

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
  input                                    clk_i,
  input                                    rst_ni,
  input                                    rst_shadowed_ni,
  input                                    clk_edn_i,
  input                                    rst_edn_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                tl_i,
  output tlul_pkg::tl_d2h_t                tl_o,
  // Interrupt Requests
  output logic                             intr_classa_o,
  output logic                             intr_classb_o,
  output logic                             intr_classc_o,
  output logic                             intr_classd_o,
  // Clock gating and reset info from rstmgr and clkmgr
  // SEC_CM: LPG.INTERSIG.MUBI
  input  prim_mubi_pkg::mubi4_t [NLpg-1:0] lpg_cg_en_i,
  input  prim_mubi_pkg::mubi4_t [NLpg-1:0] lpg_rst_en_i,
  // State information for HW crashdump
  output alert_crashdump_t                 crashdump_o,
  // Entropy Input
  output edn_pkg::edn_req_t                edn_o,
  input  edn_pkg::edn_rsp_t                edn_i,
  // Alert Sources
  // SEC_CM: ALERT.INTERSIG.DIFF
  input  alert_tx_t [NAlerts-1:0]          alert_tx_i,
  output alert_rx_t [NAlerts-1:0]          alert_rx_o,
  // Escalation outputs
  // SEC_CM: ESC.INTERSIG.DIFF
  input  esc_rx_t [N_ESC_SEV-1:0]          esc_rx_i,
  output esc_tx_t [N_ESC_SEV-1:0]          esc_tx_o
);

  //////////////////////////////////
  // Regfile Breakout and Mapping //
  //////////////////////////////////

  logic [N_CLASSES-1:0] latch_crashdump;
  logic [N_LOC_ALERT-1:0] loc_alert_trig;
  logic [N_CLASSES-1:0] irq;
  hw2reg_wrap_t hw2reg_wrap;
  reg2hw_wrap_t reg2hw_wrap;

  assign {intr_classd_o,
          intr_classc_o,
          intr_classb_o,
          intr_classa_o} = irq;

  // SEC_CM: CONFIG.SHADOW
  // SEC_CM: PING_TIMER.CONFIG.REGWEN
  // SEC_CM: ALERT.CONFIG.REGWEN
  // SEC_CM: ALERT_LOC.CONFIG.REGWEN
  // SEC_CM: CLASS.CONFIG.REGWEN
  alert_handler_reg_wrap u_reg_wrap (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i,
    .tl_o,
    .irq_o ( irq ),
    .latch_crashdump_i ( latch_crashdump ),
    .crashdump_o,
    .hw2reg_wrap,
    .reg2hw_wrap,
    // SEC_CM: BUS.INTEGRITY
    .fatal_integ_alert_o(loc_alert_trig[4])
  );

  // SEC_CM: CONFIG.SHADOW
  assign loc_alert_trig[5] = reg2hw_wrap.shadowed_err_update;
  assign loc_alert_trig[6] = reg2hw_wrap.shadowed_err_storage;

  ////////////////
  // Ping Timer //
  ////////////////

  logic [NAlerts-1:0]   alert_ping_req;
  logic [NAlerts-1:0]   alert_ping_ok;
  logic [N_ESC_SEV-1:0] esc_ping_req;
  logic [N_ESC_SEV-1:0] esc_ping_ok;

  logic edn_req, edn_ack;
  logic [LfsrWidth-1:0] edn_data;

  prim_edn_req #(
    .OutWidth(LfsrWidth)
  ) u_edn_req (
    // Alert handler side
    .clk_i,
    .rst_ni,
    .req_chk_i   ( 1'b1     ),
    .req_i       ( edn_req  ),
    .ack_o       ( edn_ack  ),
    .data_o      ( edn_data ),
    .fips_o      (          ),
    .err_o       (          ),
    // EDN side
    .clk_edn_i,
    .rst_edn_ni,
    .edn_o       ( edn_o    ),
    .edn_i       ( edn_i    )
  );

  alert_handler_ping_timer #(
    .RndCnstLfsrSeed(RndCnstLfsrSeed),
    .RndCnstLfsrPerm(RndCnstLfsrPerm)
  ) u_ping_timer (
    .clk_i,
    .rst_ni,
    .edn_req_o          ( edn_req                        ),
    .edn_ack_i          ( edn_ack                        ),
    .edn_data_i         ( edn_data                       ),
    .en_i               ( reg2hw_wrap.ping_enable        ),
    .alert_ping_en_i    ( reg2hw_wrap.alert_ping_en      ),
    .ping_timeout_cyc_i ( reg2hw_wrap.ping_timeout_cyc   ),
    // set this to the maximum width in the design.
    // can be overridden in DV and FPV to shorten the wait periods.
    // note however that this needs to be a right-aligned mask.
    // also, do not set this to a value lower than 0x7.
    .wait_cyc_mask_i    ( {PING_CNT_DW{1'b1}}            ),
    // SEC_CM: ALERT_RX.INTERSIG.BKGN_CHK
    .alert_ping_req_o   ( alert_ping_req                 ),
    // SEC_CM: ESC_TX.INTERSIG.BKGN_CHK
    .esc_ping_req_o     ( esc_ping_req                   ),
    .alert_ping_ok_i    ( alert_ping_ok                  ),
    .esc_ping_ok_i      ( esc_ping_ok                    ),
    .alert_ping_fail_o  ( loc_alert_trig[0]              ),
    .esc_ping_fail_o    ( loc_alert_trig[1]              )
  );

  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(PingTimerEscCnterCheck_A,
      u_ping_timer.u_prim_count_esc_cnt,
      loc_alert_trig[0] & loc_alert_trig[1],
      (reg2hw_wrap.ping_enable == 0))
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(PingTimerCnterCheck_A,
      u_ping_timer.u_prim_count_cnt,
      loc_alert_trig[0] & loc_alert_trig[1],
      (reg2hw_wrap.ping_enable == 0))
  `ASSERT_PRIM_DOUBLE_LFSR_ERROR_TRIGGER_ERR(PingTimerDoubleLfsrCheck_A,
      u_ping_timer.u_prim_double_lfsr,
      loc_alert_trig[0] & loc_alert_trig[1],
      (reg2hw_wrap.ping_enable == 0))
  `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(PingTimerFsmCheck_A,
      u_ping_timer.u_state_regs,
      loc_alert_trig[0] & loc_alert_trig[1],
      (reg2hw_wrap.ping_enable == 0))

  /////////////////////////////
  // Low-power group control //
  /////////////////////////////

  prim_mubi_pkg::mubi4_t [NAlerts-1:0] alert_init_trig;
  alert_handler_lpg_ctrl u_alert_handler_lpg_ctrl (
    .clk_i,
    .rst_ni,
    // SEC_CM: LPG.INTERSIG.MUBI
    .lpg_cg_en_i,
    .lpg_rst_en_i,
    .alert_init_trig_o ( alert_init_trig )
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
    ) u_alert_receiver (
      .clk_i,
      .rst_ni,
      .init_trig_i  ( alert_init_trig[k] ),
      .ping_req_i   ( alert_ping_req[k]  ),
      .ping_ok_o    ( alert_ping_ok[k]   ),
      .integ_fail_o ( alert_integfail[k] ),
      .alert_o      ( alert_trig[k]      ),
      // SEC_CM: ALERT.INTERSIG.DIFF
      .alert_rx_o   ( alert_rx_o[k]      ),
      .alert_tx_i   ( alert_tx_i[k]      )
    );
  end

  assign loc_alert_trig[2] = |(reg2hw_wrap.alert_en & alert_integfail);

  ///////////////////////////////////////
  // Set alert cause bits and classify //
  ///////////////////////////////////////

  alert_handler_class u_class (
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

  logic [N_CLASSES-1:0][N_ESC_SEV-1:0] class_esc_sig_req;

  for (genvar k = 0; k < N_CLASSES; k++) begin : gen_classes
    logic class_accu_fail, class_accu_trig;
    alert_handler_accu u_accu (
      .clk_i,
      .rst_ni,
      .class_en_i    ( reg2hw_wrap.class_en[k]           ),
      .clr_i         ( reg2hw_wrap.class_clr[k]          ),
      .class_trig_i  ( hw2reg_wrap.class_trig[k]         ),
      .thresh_i      ( reg2hw_wrap.class_accum_thresh[k] ),
      .accu_cnt_o    ( hw2reg_wrap.class_accum_cnt[k]    ),
      .accu_trig_o   ( class_accu_trig                   ),
      .accu_fail_o   ( class_accu_fail                   )
    );
    `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(AccuCnterCheck_A,
        u_accu.u_prim_count,
        esc_tx_o[0].esc_p & esc_tx_o[1].esc_p & esc_tx_o[2].esc_p & esc_tx_o[3].esc_p)

    alert_handler_esc_timer u_esc_timer (
      .clk_i,
      .rst_ni,
      .en_i              ( reg2hw_wrap.class_en[k]              ),
      // this clear does not apply to interrupts
      .clr_i             ( reg2hw_wrap.class_clr[k]             ),
      // an interrupt enables the timeout
      .timeout_en_i      ( irq[k]                               ),
      .accu_trig_i       ( class_accu_trig                      ),
      .accu_fail_i       ( class_accu_fail                      ),
      .timeout_cyc_i     ( reg2hw_wrap.class_timeout_cyc[k]     ),
      .esc_en_i          ( reg2hw_wrap.class_esc_en[k]          ),
      .esc_map_i         ( reg2hw_wrap.class_esc_map[k]         ),
      .phase_cyc_i       ( reg2hw_wrap.class_phase_cyc[k]       ),
      .crashdump_phase_i ( reg2hw_wrap.class_crashdump_phase[k] ),
      .latch_crashdump_o ( latch_crashdump[k]                   ),
      .esc_trig_o        ( hw2reg_wrap.class_esc_trig[k]        ),
      .esc_cnt_o         ( hw2reg_wrap.class_esc_cnt[k]         ),
      .esc_state_o       ( hw2reg_wrap.class_esc_state[k]       ),
      .esc_sig_req_o     ( class_esc_sig_req[k]                 )
    );

    `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ERR(EscTimerCnterCheck_A,
        u_esc_timer.u_prim_count,
        esc_tx_o[0].esc_p & esc_tx_o[1].esc_p & esc_tx_o[2].esc_p & esc_tx_o[3].esc_p)
    `ASSERT_PRIM_FSM_ERROR_TRIGGER_ERR(EscTimerFsmCheck_A,
        u_esc_timer.u_state_regs,
        esc_tx_o[0].esc_p & esc_tx_o[1].esc_p & esc_tx_o[2].esc_p & esc_tx_o[3].esc_p)
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
    // SEC_CM: ESC_RX.INTERSIG.BKGN_CHK
    // Note: This countermeasure is actually implemented on the receiver side. We currently cannot
    // put this RTL label inside that module due to the way our countermeasure annotation check
    // script discovers the RTL files. The label is thus put here. Please refer to
    // prim_esc_receiver.sv for the actual implementation of this mechanism.
    prim_esc_sender u_esc_sender (
      .clk_i,
      .rst_ni,
      .ping_req_i   ( esc_ping_req[k]  ),
      .ping_ok_o    ( esc_ping_ok[k]   ),
      .integ_fail_o ( esc_integfail[k] ),
      .esc_req_i    ( esc_sig_req[k]   ),
      // SEC_CM: ESC.INTERSIG.DIFF
      .esc_rx_i     ( esc_rx_i[k]      ),
      .esc_tx_o     ( esc_tx_o[k]      )
    );
  end

  assign loc_alert_trig[3] = |esc_integfail;

  ////////////////
  // Assertions //
  ////////////////

  // check whether all outputs have a good known state after reset
  `ASSERT_KNOWN(TlDValidKnownO_A,  tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A,  tl_o.a_ready)
  `ASSERT_KNOWN(IrqAKnownO_A,      intr_classa_o)
  `ASSERT_KNOWN(IrqBKnownO_A,      intr_classb_o)
  `ASSERT_KNOWN(IrqCKnownO_A,      intr_classc_o)
  `ASSERT_KNOWN(IrqDKnownO_A,      intr_classd_o)
  `ASSERT_KNOWN(CrashdumpKnownO_A, crashdump_o)
  `ASSERT_KNOWN(AckPKnownO_A,      alert_rx_o)
  `ASSERT_KNOWN(EscPKnownO_A,      esc_tx_o)
  `ASSERT_KNOWN(EdnKnownO_A,       edn_o)

  // this restriction is due to specifics in the ping selection mechanism
  `ASSERT_INIT(CheckNAlerts,   NAlerts  < (256 - N_CLASSES))
  `ASSERT_INIT(CheckEscCntDw,  EscCntDw  <= 32)
  `ASSERT_INIT(CheckAccuCntDw, AccuCntDw <= 32)
  `ASSERT_INIT(CheckNClasses,  N_CLASSES <= 8)
  `ASSERT_INIT(CheckNEscSev,   N_ESC_SEV <= 8)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ERR(RegWeOnehotCheck_A,
      u_reg_wrap.u_reg, loc_alert_trig[4])
endmodule
