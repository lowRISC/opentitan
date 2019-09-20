// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Breakout / remapping wrapper for register file. Generated from template.

module alert_handler_reg_wrap (
  input                                   clk_i,
  input                                   rst_ni,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t               tl_i,
  output tlul_pkg::tl_d2h_t               tl_o,
  // interrupt
  output logic [alert_pkg::N_CLASSES-1:0] irq_o,
  // hw2reg
  input  alert_pkg::hw2reg_wrap_t         hw2reg_wrap,
  // reg2hw
  output alert_pkg::reg2hw_wrap_t         reg2hw_wrap
);

  //////////////////////////////////////////////////////
  // reg instance
  //////////////////////////////////////////////////////

  logic [alert_pkg::N_CLASSES-1:0] class_autolock_en;
  alert_handler_reg_pkg::alert_handler_reg2hw_t reg2hw;
  alert_handler_reg_pkg::alert_handler_hw2reg_t hw2reg;

  alert_handler_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg
  );

  //////////////////////////////////////////////////////
  // interrupts
  //////////////////////////////////////////////////////
<% label = ['classa','classb', 'classc', 'classd'] %>
%for k in range(n_classes):
    prim_intr_hw #(
      .Width(1)
    ) i_irq_${label[k]} (
      .event_intr_i           ( hw2reg_wrap.class_trig[${k}] & reg2hw_wrap.class_en[${k}] ),
      .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.${label[k]}.q  ),
      .reg2hw_intr_test_q_i   ( reg2hw.intr_test.${label[k]}.q    ),
      .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.${label[k]}.qe   ),
      .reg2hw_intr_state_q_i  ( reg2hw.intr_state.${label[k]}.q   ),
      .hw2reg_intr_state_de_o ( hw2reg.intr_state.${label[k]}.de  ),
      .hw2reg_intr_state_d_o  ( hw2reg.intr_state.${label[k]}.d   ),
      .intr_o                 ( irq_o[${k}]                     )
    );

%endfor
  //////////////////////////////////////////////////////
  // hw2reg mappings
  //////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////
  // if an alert is enabled and it fires,
  // we have to set the corresponding cause bit
<%
prefix = '  assign { '
space  = '';
for k in range(len(prefix)):
  space += ' '
comma = ','
w = '' %>
%for k in range(n_alerts-1,-1,-1):
<%
if n_alerts > reg_dw:
  w = int(k / reg_dw)
if not k:
  comma = ''
if k < n_alerts-1:
  prefix = space;%>${prefix}hw2reg.cause_word${w}.a${k}.d${comma}
%endfor
${space}} = '1;
<%
prefix = '  assign { '
space  = '';
for k in range(len(prefix)):
  space += ' '
comma = ','
w = '' %>

%for k in range(n_alerts-1,-1,-1):
<%
if n_alerts > reg_dw:
  w = int(k / reg_dw)
if not k:
  comma = ''
if k < n_alerts-1:
  prefix = space;%>${prefix}hw2reg.cause_word${w}.a${k}.de${comma}
%endfor
${space}} = hw2reg_wrap.alert_cause;
  //----------------------------------------------------------------------------

  // if a local alert is enabled and it fires,
  // we have to set the corresponding cause bit
  assign { hw2reg.cause_local.la3.d,
           hw2reg.cause_local.la2.d,
           hw2reg.cause_local.la1.d,
           hw2reg.cause_local.la0.d } = '1;

  assign { hw2reg.cause_local.la3.de,
           hw2reg.cause_local.la2.de,
           hw2reg.cause_local.la1.de,
           hw2reg.cause_local.la0.de } = hw2reg_wrap.loc_alert_cause;

  // autolock can clear these regs automatically upon entering escalation
  // note: the class must be activated for this to occur
  assign { hw2reg.classd_clren.d,
           hw2reg.classc_clren.d,
           hw2reg.classb_clren.d,
           hw2reg.classa_clren.d } = '0;

  assign { hw2reg.classd_clren.de,
           hw2reg.classc_clren.de,
           hw2reg.classb_clren.de,
           hw2reg.classa_clren.de } = hw2reg_wrap.class_esc_trig    &
                                      class_autolock_en             &
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

  //////////////////////////////////////////////////////
  // reg2hw mappings
  //////////////////////////////////////////////////////

  // config register lock
  assign reg2hw_wrap.config_locked = ~reg2hw.regen.q;

  //////////////////////////////////////////////////////////////////////////////
  // alert enable
<%
prefix = '  assign reg2hw_wrap.alert_en = { '
space  = '';
for k in range(len(prefix)):
  space += ' '
comma = ','
w = '' %>
%for k in range(n_alerts-1,-1,-1):
<%
if n_alerts > (reg_dw/4):
  w = int(k / (reg_dw/4))
if not k:
  comma = ' };'
if k < n_alerts-1:
  prefix = space;%>${prefix}reg2hw.alert_en${w}.en_a${k}.q${comma}
%endfor
  //----------------------------------------------------------------------------

  //////////////////////////////////////////////////////////////////////////////
  // classification mapping
<%
prefix = '  assign reg2hw_wrap.alert_class = { '
space  = '';
for k in range(len(prefix)):
  space += ' '
comma = ','
w = '' %>
%for k in range(n_alerts-1,-1,-1):
<%
if n_alerts > (reg_dw/4):
  w = int(k / (reg_dw/4))
if not k:
  comma = ' };'
if k < n_alerts-1:
  prefix = space;%>${prefix}reg2hw.alert_class${w}.class_a${k}.q${comma}
%endfor
  //----------------------------------------------------------------------------

  // local alert enable and class assignments
  assign reg2hw_wrap.loc_alert_en = { reg2hw.loc_alert_en.en_la3.q,
                                      reg2hw.loc_alert_en.en_la2.q,
                                      reg2hw.loc_alert_en.en_la1.q,
                                      reg2hw.loc_alert_en.en_la0.q };

  assign reg2hw_wrap.loc_alert_class = { reg2hw.loc_alert_class.class_la3.q[1:0],
                                         reg2hw.loc_alert_class.class_la2.q[1:0],
                                         reg2hw.loc_alert_class.class_la1.q[1:0],
                                         reg2hw.loc_alert_class.class_la0.q[1:0]};
  // ping timeout in cycles
  assign reg2hw_wrap.ping_timeout_cyc = reg2hw.ping_timeout_cyc.q;

  // class enable
  assign reg2hw_wrap.class_en = { reg2hw.classd_ctrl.en,
                                  reg2hw.classc_ctrl.en,
                                  reg2hw.classb_ctrl.en,
                                  reg2hw.classa_ctrl.en };

  // autolock enable
  assign class_autolock_en = { reg2hw.classd_ctrl.lock,
                               reg2hw.classc_ctrl.lock,
                               reg2hw.classb_ctrl.lock,
                               reg2hw.classa_ctrl.lock };

  // escalation signal enable
  assign reg2hw_wrap.class_esc_en = { reg2hw.classd_ctrl.en_e3,
                                      reg2hw.classd_ctrl.en_e2,
                                      reg2hw.classd_ctrl.en_e1,
                                      reg2hw.classd_ctrl.en_e0,
                                      //
                                      reg2hw.classc_ctrl.en_e3,
                                      reg2hw.classc_ctrl.en_e2,
                                      reg2hw.classc_ctrl.en_e1,
                                      reg2hw.classc_ctrl.en_e0,
                                      //
                                      reg2hw.classb_ctrl.en_e3,
                                      reg2hw.classb_ctrl.en_e2,
                                      reg2hw.classb_ctrl.en_e1,
                                      reg2hw.classb_ctrl.en_e0,
                                      //
                                      reg2hw.classa_ctrl.en_e3,
                                      reg2hw.classa_ctrl.en_e2,
                                      reg2hw.classa_ctrl.en_e1,
                                      reg2hw.classa_ctrl.en_e0 };


  // escalation phase to escalation signal mapping
  assign reg2hw_wrap.class_esc_map = { reg2hw.classd_ctrl.map_e3,
                                       reg2hw.classd_ctrl.map_e2,
                                       reg2hw.classd_ctrl.map_e1,
                                       reg2hw.classd_ctrl.map_e0,
                                       //
                                       reg2hw.classc_ctrl.map_e3,
                                       reg2hw.classc_ctrl.map_e2,
                                       reg2hw.classc_ctrl.map_e1,
                                       reg2hw.classc_ctrl.map_e0,
                                       //
                                       reg2hw.classb_ctrl.map_e3,
                                       reg2hw.classb_ctrl.map_e2,
                                       reg2hw.classb_ctrl.map_e1,
                                       reg2hw.classb_ctrl.map_e0,
                                       //
                                       reg2hw.classa_ctrl.map_e3,
                                       reg2hw.classa_ctrl.map_e2,
                                       reg2hw.classa_ctrl.map_e1,
                                       reg2hw.classa_ctrl.map_e0 };

  // TODO: check whether this is correctly locked inside the regfile
  // writing 1b1 to a class clr register clears the accumulator and
  // escalation state if autolock is not asserted
  assign reg2hw_wrap.class_clr = { reg2hw.classd_clr.q & reg2hw.classd_clr.qe,
                                   reg2hw.classc_clr.q & reg2hw.classc_clr.qe,
                                   reg2hw.classb_clr.q & reg2hw.classb_clr.qe,
                                   reg2hw.classa_clr.q & reg2hw.classa_clr.qe };

  // accumulator thresholds
  assign reg2hw_wrap.class_accum_thresh = { reg2hw.classd_accum_thresh.q,
                                            reg2hw.classc_accum_thresh.q,
                                            reg2hw.classb_accum_thresh.q,
                                            reg2hw.classa_accum_thresh.q };

  // interrupt timeout lengths
  assign reg2hw_wrap.class_timeout_cyc = { reg2hw.classd_timeout_cyc.q,
                                           reg2hw.classc_timeout_cyc.q,
                                           reg2hw.classb_timeout_cyc.q,
                                           reg2hw.classa_timeout_cyc.q };
  // escalation phase lengths
  assign reg2hw_wrap.class_phase_cyc = { reg2hw.classd_phase3_cyc.q,
                                         reg2hw.classd_phase2_cyc.q,
                                         reg2hw.classd_phase1_cyc.q,
                                         reg2hw.classd_phase0_cyc.q,
                                         //
                                         reg2hw.classc_phase3_cyc.q,
                                         reg2hw.classc_phase2_cyc.q,
                                         reg2hw.classc_phase1_cyc.q,
                                         reg2hw.classc_phase0_cyc.q,
                                         //
                                         reg2hw.classb_phase3_cyc.q,
                                         reg2hw.classb_phase2_cyc.q,
                                         reg2hw.classb_phase1_cyc.q,
                                         reg2hw.classb_phase0_cyc.q,
                                         //
                                         reg2hw.classa_phase3_cyc.q,
                                         reg2hw.classa_phase2_cyc.q,
                                         reg2hw.classa_phase1_cyc.q,
                                         reg2hw.classa_phase0_cyc.q};

endmodule : alert_handler_reg_wrap
