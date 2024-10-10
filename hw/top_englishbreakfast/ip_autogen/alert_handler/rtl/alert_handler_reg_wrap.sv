// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Breakout / remapping wrapper for register file.

module alert_handler_reg_wrap import alert_pkg::*; (
  input                                   clk_i,
  input                                   rst_ni,
  input                                   rst_shadowed_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t               tl_i,
  output tlul_pkg::tl_d2h_t               tl_o,
  // interrupt
  output logic [N_CLASSES-1:0] irq_o,
  // State information for HW crashdump
  input  [N_CLASSES-1:0]       latch_crashdump_i,
  output alert_crashdump_t     crashdump_o,
  // hw2reg
  input  hw2reg_wrap_t         hw2reg_wrap,
  // reg2hw
  output reg2hw_wrap_t         reg2hw_wrap,
  // bus integrity alert
  output logic                 fatal_integ_alert_o
);


  //////////////////
  // reg instance //
  //////////////////

  logic [N_CLASSES-1:0] class_autolock_en;
  alert_handler_reg_pkg::alert_handler_reg2hw_t reg2hw;
  alert_handler_reg_pkg::alert_handler_hw2reg_t hw2reg;

  alert_handler_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .rst_shadowed_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .shadowed_storage_err_o(reg2hw_wrap.shadowed_err_storage),
    .shadowed_update_err_o(reg2hw_wrap.shadowed_err_update),
    .intg_err_o(fatal_integ_alert_o)
  );

  ////////////////
  // interrupts //
  ////////////////

    prim_intr_hw #(
      .Width(1)
    ) u_irq_classa (
      .clk_i,
      .rst_ni,
      .event_intr_i           ( hw2reg_wrap.class_trig[0]    ),
      .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.classa.q  ),
      .reg2hw_intr_test_q_i   ( reg2hw.intr_test.classa.q    ),
      .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.classa.qe   ),
      .reg2hw_intr_state_q_i  ( reg2hw.intr_state.classa.q   ),
      .hw2reg_intr_state_de_o ( hw2reg.intr_state.classa.de  ),
      .hw2reg_intr_state_d_o  ( hw2reg.intr_state.classa.d   ),
      .intr_o                 ( irq_o[0]                     )
    );

    prim_intr_hw #(
      .Width(1)
    ) u_irq_classb (
      .clk_i,
      .rst_ni,
      .event_intr_i           ( hw2reg_wrap.class_trig[1]    ),
      .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.classb.q  ),
      .reg2hw_intr_test_q_i   ( reg2hw.intr_test.classb.q    ),
      .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.classb.qe   ),
      .reg2hw_intr_state_q_i  ( reg2hw.intr_state.classb.q   ),
      .hw2reg_intr_state_de_o ( hw2reg.intr_state.classb.de  ),
      .hw2reg_intr_state_d_o  ( hw2reg.intr_state.classb.d   ),
      .intr_o                 ( irq_o[1]                     )
    );

    prim_intr_hw #(
      .Width(1)
    ) u_irq_classc (
      .clk_i,
      .rst_ni,
      .event_intr_i           ( hw2reg_wrap.class_trig[2]    ),
      .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.classc.q  ),
      .reg2hw_intr_test_q_i   ( reg2hw.intr_test.classc.q    ),
      .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.classc.qe   ),
      .reg2hw_intr_state_q_i  ( reg2hw.intr_state.classc.q   ),
      .hw2reg_intr_state_de_o ( hw2reg.intr_state.classc.de  ),
      .hw2reg_intr_state_d_o  ( hw2reg.intr_state.classc.d   ),
      .intr_o                 ( irq_o[2]                     )
    );

    prim_intr_hw #(
      .Width(1)
    ) u_irq_classd (
      .clk_i,
      .rst_ni,
      .event_intr_i           ( hw2reg_wrap.class_trig[3]    ),
      .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.classd.q  ),
      .reg2hw_intr_test_q_i   ( reg2hw.intr_test.classd.q    ),
      .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.classd.qe   ),
      .reg2hw_intr_state_q_i  ( reg2hw.intr_state.classd.q   ),
      .hw2reg_intr_state_de_o ( hw2reg.intr_state.classd.de  ),
      .hw2reg_intr_state_d_o  ( hw2reg.intr_state.classd.d   ),
      .intr_o                 ( irq_o[3]                     )
    );

  /////////////////////
  // hw2reg mappings //
  /////////////////////

  // if an alert is enabled and it fires,
  // we have to set the corresponding cause bit
  for (genvar k = 0; k < NAlerts; k++) begin : gen_alert_cause
    assign hw2reg.alert_cause[k].d  = 1'b1;
    assign hw2reg.alert_cause[k].de = reg2hw.alert_cause[k].q |
                                      hw2reg_wrap.alert_cause[k];
  end

  // if a local alert is enabled and it fires,
  // we have to set the corresponding cause bit
  for (genvar k = 0; k < N_LOC_ALERT; k++) begin : gen_loc_alert_cause
    assign hw2reg.loc_alert_cause[k].d  = 1'b1;
    assign hw2reg.loc_alert_cause[k].de = reg2hw.loc_alert_cause[k].q |
                                          hw2reg_wrap.loc_alert_cause[k];
  end

  // ping timeout in cycles
  // autolock can clear these regs automatically upon entering escalation
  // note: the class must be activated for this to occur
  assign { hw2reg.classd_clr_regwen.d,
           hw2reg.classc_clr_regwen.d,
           hw2reg.classb_clr_regwen.d,
           hw2reg.classa_clr_regwen.d } = '0;

  assign { hw2reg.classd_clr_regwen.de,
           hw2reg.classc_clr_regwen.de,
           hw2reg.classb_clr_regwen.de,
           hw2reg.classa_clr_regwen.de } = hw2reg_wrap.class_esc_trig &
                                           class_autolock_en          &
                                           reg2hw_wrap.class_en;

  // current accumulator counts
  assign { hw2reg.classd_accum_cnt.d,
           hw2reg.classc_accum_cnt.d,
           hw2reg.classb_accum_cnt.d,
           hw2reg.classa_accum_cnt.d } = hw2reg_wrap.class_accum_cnt;

  // current accumulator counts
  assign { hw2reg.classd_esc_cnt.d,
           hw2reg.classc_esc_cnt.d,
           hw2reg.classb_esc_cnt.d,
           hw2reg.classa_esc_cnt.d } = hw2reg_wrap.class_esc_cnt;

  // current accumulator counts
  assign { hw2reg.classd_state.d,
           hw2reg.classc_state.d,
           hw2reg.classb_state.d,
           hw2reg.classa_state.d } = hw2reg_wrap.class_esc_state;

  /////////////////////
  // reg2hw mappings //
  /////////////////////

  // config register lock
  assign reg2hw_wrap.ping_enable = reg2hw.ping_timer_en_shadowed.q;

  // alert enable and class assignments
  for (genvar k = 0; k < NAlerts; k++) begin : gen_alert_en_class
    // we only ping enabled alerts that are locked
    assign reg2hw_wrap.alert_ping_en[k] = reg2hw.alert_en_shadowed[k].q &
                                          ~reg2hw.alert_regwen[k].q;
    assign reg2hw_wrap.alert_en[k]      = reg2hw.alert_en_shadowed[k].q;
    assign reg2hw_wrap.alert_class[k]   = reg2hw.alert_class_shadowed[k].q;
  end

  // local alert enable and class assignments
  for (genvar k = 0; k < N_LOC_ALERT; k++) begin : gen_loc_alert_en_class
    assign reg2hw_wrap.loc_alert_en[k]    = reg2hw.loc_alert_en_shadowed[k].q;
    assign reg2hw_wrap.loc_alert_class[k] = reg2hw.loc_alert_class_shadowed[k].q;
  end

  assign reg2hw_wrap.ping_timeout_cyc = reg2hw.ping_timeout_cyc_shadowed.q;

  // class enable
  // we require that at least one of the enable signals is
  // set for a class to be enabled
  assign reg2hw_wrap.class_en = {
    reg2hw.classd_ctrl_shadowed.en.q & ( reg2hw.classd_ctrl_shadowed.en_e3.q |
                                         reg2hw.classd_ctrl_shadowed.en_e2.q |
                                         reg2hw.classd_ctrl_shadowed.en_e1.q |
                                         reg2hw.classd_ctrl_shadowed.en_e0.q ),
    //
    reg2hw.classc_ctrl_shadowed.en.q & ( reg2hw.classc_ctrl_shadowed.en_e3.q |
                                         reg2hw.classc_ctrl_shadowed.en_e2.q |
                                         reg2hw.classc_ctrl_shadowed.en_e1.q |
                                         reg2hw.classc_ctrl_shadowed.en_e0.q ),
    //
    reg2hw.classb_ctrl_shadowed.en.q & ( reg2hw.classb_ctrl_shadowed.en_e3.q |
                                         reg2hw.classb_ctrl_shadowed.en_e2.q |
                                         reg2hw.classb_ctrl_shadowed.en_e1.q |
                                         reg2hw.classb_ctrl_shadowed.en_e0.q ),
    //
    reg2hw.classa_ctrl_shadowed.en.q & ( reg2hw.classa_ctrl_shadowed.en_e3.q |
                                         reg2hw.classa_ctrl_shadowed.en_e2.q |
                                         reg2hw.classa_ctrl_shadowed.en_e1.q |
                                         reg2hw.classa_ctrl_shadowed.en_e0.q )
  };


  // autolock enable
  assign class_autolock_en = { reg2hw.classd_ctrl_shadowed.lock.q,
                               reg2hw.classc_ctrl_shadowed.lock.q,
                               reg2hw.classb_ctrl_shadowed.lock.q,
                               reg2hw.classa_ctrl_shadowed.lock.q };

  // escalation signal enable
  assign reg2hw_wrap.class_esc_en = { reg2hw.classd_ctrl_shadowed.en_e3.q,
                                      reg2hw.classd_ctrl_shadowed.en_e2.q,
                                      reg2hw.classd_ctrl_shadowed.en_e1.q,
                                      reg2hw.classd_ctrl_shadowed.en_e0.q,
                                      //
                                      reg2hw.classc_ctrl_shadowed.en_e3.q,
                                      reg2hw.classc_ctrl_shadowed.en_e2.q,
                                      reg2hw.classc_ctrl_shadowed.en_e1.q,
                                      reg2hw.classc_ctrl_shadowed.en_e0.q,
                                      //
                                      reg2hw.classb_ctrl_shadowed.en_e3.q,
                                      reg2hw.classb_ctrl_shadowed.en_e2.q,
                                      reg2hw.classb_ctrl_shadowed.en_e1.q,
                                      reg2hw.classb_ctrl_shadowed.en_e0.q,
                                      //
                                      reg2hw.classa_ctrl_shadowed.en_e3.q,
                                      reg2hw.classa_ctrl_shadowed.en_e2.q,
                                      reg2hw.classa_ctrl_shadowed.en_e1.q,
                                      reg2hw.classa_ctrl_shadowed.en_e0.q };


  // escalation phase to escalation signal mapping
  assign reg2hw_wrap.class_esc_map = { reg2hw.classd_ctrl_shadowed.map_e3.q,
                                       reg2hw.classd_ctrl_shadowed.map_e2.q,
                                       reg2hw.classd_ctrl_shadowed.map_e1.q,
                                       reg2hw.classd_ctrl_shadowed.map_e0.q,
                                       //
                                       reg2hw.classc_ctrl_shadowed.map_e3.q,
                                       reg2hw.classc_ctrl_shadowed.map_e2.q,
                                       reg2hw.classc_ctrl_shadowed.map_e1.q,
                                       reg2hw.classc_ctrl_shadowed.map_e0.q,
                                       //
                                       reg2hw.classb_ctrl_shadowed.map_e3.q,
                                       reg2hw.classb_ctrl_shadowed.map_e2.q,
                                       reg2hw.classb_ctrl_shadowed.map_e1.q,
                                       reg2hw.classb_ctrl_shadowed.map_e0.q,
                                       //
                                       reg2hw.classa_ctrl_shadowed.map_e3.q,
                                       reg2hw.classa_ctrl_shadowed.map_e2.q,
                                       reg2hw.classa_ctrl_shadowed.map_e1.q,
                                       reg2hw.classa_ctrl_shadowed.map_e0.q };

  // Determines in which phase to latch the crashdump.
  assign reg2hw_wrap.class_crashdump_phase = { reg2hw.classd_crashdump_trigger_shadowed.q,
                                               reg2hw.classc_crashdump_trigger_shadowed.q,
                                               reg2hw.classb_crashdump_trigger_shadowed.q,
                                               reg2hw.classa_crashdump_trigger_shadowed.q };

  // writing 1b1 to a class clr register clears the accumulator and
  // escalation state if autolock is not asserted
  assign reg2hw_wrap.class_clr = { reg2hw.classd_clr_shadowed.q & reg2hw.classd_clr_shadowed.qe,
                                   reg2hw.classc_clr_shadowed.q & reg2hw.classc_clr_shadowed.qe,
                                   reg2hw.classb_clr_shadowed.q & reg2hw.classb_clr_shadowed.qe,
                                   reg2hw.classa_clr_shadowed.q & reg2hw.classa_clr_shadowed.qe };


  // accumulator thresholds
  assign reg2hw_wrap.class_accum_thresh = { reg2hw.classd_accum_thresh_shadowed.q,
                                            reg2hw.classc_accum_thresh_shadowed.q,
                                            reg2hw.classb_accum_thresh_shadowed.q,
                                            reg2hw.classa_accum_thresh_shadowed.q };

  // interrupt timeout lengths
  assign reg2hw_wrap.class_timeout_cyc = { reg2hw.classd_timeout_cyc_shadowed.q,
                                           reg2hw.classc_timeout_cyc_shadowed.q,
                                           reg2hw.classb_timeout_cyc_shadowed.q,
                                           reg2hw.classa_timeout_cyc_shadowed.q };
  // escalation phase lengths
  assign reg2hw_wrap.class_phase_cyc = { reg2hw.classd_phase3_cyc_shadowed.q,
                                         reg2hw.classd_phase2_cyc_shadowed.q,
                                         reg2hw.classd_phase1_cyc_shadowed.q,
                                         reg2hw.classd_phase0_cyc_shadowed.q,
                                         //
                                         reg2hw.classc_phase3_cyc_shadowed.q,
                                         reg2hw.classc_phase2_cyc_shadowed.q,
                                         reg2hw.classc_phase1_cyc_shadowed.q,
                                         reg2hw.classc_phase0_cyc_shadowed.q,
                                         //
                                         reg2hw.classb_phase3_cyc_shadowed.q,
                                         reg2hw.classb_phase2_cyc_shadowed.q,
                                         reg2hw.classb_phase1_cyc_shadowed.q,
                                         reg2hw.classb_phase0_cyc_shadowed.q,
                                         //
                                         reg2hw.classa_phase3_cyc_shadowed.q,
                                         reg2hw.classa_phase2_cyc_shadowed.q,
                                         reg2hw.classa_phase1_cyc_shadowed.q,
                                         reg2hw.classa_phase0_cyc_shadowed.q};

  //////////////////////
  // crashdump output //
  //////////////////////

  logic [N_CLASSES-1:0] crashdump_latched_q;
  alert_crashdump_t crashdump_d, crashdump_q;

  // alert cause output
  for (genvar k = 0; k < NAlerts; k++) begin : gen_alert_cause_dump
    assign crashdump_d.alert_cause[k]  = reg2hw.alert_cause[k].q;
  end

  // local alert cause register output
  for (genvar k = 0; k < N_LOC_ALERT; k++) begin : gen_loc_alert_cause_dump
    assign crashdump_d.loc_alert_cause[k]  = reg2hw.loc_alert_cause[k].q;
  end

  assign crashdump_d.class_accum_cnt = hw2reg_wrap.class_accum_cnt;
  assign crashdump_d.class_esc_cnt   = hw2reg_wrap.class_esc_cnt;
  assign crashdump_d.class_esc_state = hw2reg_wrap.class_esc_state;

  // We latch the crashdump upon triggering any of the escalation protocols. The reason for this is
  // that during escalation, certain alert senders may start to trigger due to FSMs being moved
  // into escalation mode - thereby masking the actual alert reasons exposed in the cause
  // registers.
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_crashdump
    if (!rst_ni) begin
      crashdump_latched_q <= '0;
      crashdump_q <= '0;
    end else begin
      // We track which class has been escalated so that the crashdump latching mechanism cannot be
      // re-armed by clearing another class that has not escalated yet. This also implies that if
      // an unclearable class has escalated, the crashdump latching mechanism cannot be re-armed.
      crashdump_latched_q <= (crashdump_latched_q & ~reg2hw_wrap.class_clr) | latch_crashdump_i;

      // The alert handler only captures the first escalation event that asserts a latch_crashdump_i
      // signal, unless all classes are cleared, in which case the crashdump latching mechanism is
      // re-armed. In other words, we latch the crashdump if any of the latch_crashdump_i bits is
      // asserted, and no crashdump has been latched yet.
      if (|latch_crashdump_i && !(|crashdump_latched_q)) begin
        crashdump_q <= crashdump_d;
      end
    end
  end

  // As long as the crashdump has not been latched yet, we output the current alert handler state.
  // Once any of the classes has triggered the latching, we switch to the latched snapshot.
  assign crashdump_o = (|crashdump_latched_q) ? crashdump_q : crashdump_d;

endmodule : alert_handler_reg_wrap
