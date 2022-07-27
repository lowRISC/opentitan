// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// adc_ctrl core module

module adc_ctrl_core import adc_ctrl_reg_pkg::* ; (
  input  clk_aon_i,//Always-on 200KHz clock(logic)
  input  rst_aon_ni,//power-on reset for the 200KHz clock(logic)
  input  clk_i,//regular core clock for SW config interface
  input  rst_ni,//power-on hardware reset

  // register interface inputs
  input  adc_ctrl_reg2hw_t reg2hw_i,

  // register interface outputs
  output adc_ctrl_hw2reg_intr_state_reg_t intr_state_o,
  output adc_ctrl_hw2reg_adc_chn_val_mreg_t [NumAdcChannel-1:0] adc_chn_val_o,
  output adc_ctrl_hw2reg_adc_intr_status_reg_t adc_intr_status_o,
  output adc_ctrl_hw2reg_filter_status_reg_t aon_filter_status_o,

  // interrupt and wakeup outputs
  output wkup_req_o,
  output intr_o,

  // adc interface
  input  ast_pkg::adc_ast_rsp_t adc_i,
  output ast_pkg::adc_ast_req_t adc_o
);

  logic chn0_val_we, chn1_val_we;//write enable for the latest ADC sample
  logic [9:0] chn0_val, chn1_val;

  logic [NumAdcFilter-1:0] chn0_match, chn1_match, match;
  logic [NumAdcFilter-1:0] match_pulse;

  //write enable for the ADC sample when the interrupt is triggered
  logic adc_ctrl_done, oneshot_done;

  // Pack channel 0/1 into one variable
  typedef struct packed {
    logic [9:0] min_v;
    logic [9:0] max_v;
    logic cond;
    logic en;
  } filter_ctl_t;

  filter_ctl_t [NumAdcChannel-1:0][NumAdcFilter-1:0] aon_filter_ctl;

  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_ctl_sync

    assign aon_filter_ctl[0][k] = '{
      min_v: reg2hw_i.adc_chn0_filter_ctl[k].min_v.q,
      max_v: reg2hw_i.adc_chn0_filter_ctl[k].max_v.q,
      cond:  reg2hw_i.adc_chn0_filter_ctl[k].cond.q,
      en:    reg2hw_i.adc_chn0_filter_ctl[k].en.q
    };

    assign aon_filter_ctl[1][k] = '{
      min_v: reg2hw_i.adc_chn1_filter_ctl[k].min_v.q,
      max_v: reg2hw_i.adc_chn1_filter_ctl[k].max_v.q,
      cond:  reg2hw_i.adc_chn1_filter_ctl[k].cond.q,
      en:    reg2hw_i.adc_chn1_filter_ctl[k].en.q
    };
  end // block: gen_filter_ctl_sync

  // Recent adc channel values
  assign adc_chn_val_o[0].adc_chn_value.de = chn0_val_we;
  assign adc_chn_val_o[0].adc_chn_value.d  = chn0_val;
  assign adc_chn_val_o[1].adc_chn_value.de = chn1_val_we;
  assign adc_chn_val_o[1].adc_chn_value.d  = chn1_val;

  // Interrupt based adc channel values
  // The value of the adc is captured whenever an interrupt triggers.
  // There are two cases:
  // completion of one shot mode
  // match detection from the filters
  logic chn_val_intr_we;
  assign chn_val_intr_we = reg2hw_i.adc_en_ctl.oneshot_mode.q ? oneshot_done :
                           reg2hw_i.adc_en_ctl.adc_enable.q   ? |match_pulse : '0;

  assign adc_chn_val_o[0].adc_chn_value_intr.de = chn_val_intr_we;
  assign adc_chn_val_o[0].adc_chn_value_intr.d  = chn0_val;
  assign adc_chn_val_o[1].adc_chn_value_intr.de = chn_val_intr_we;
  assign adc_chn_val_o[1].adc_chn_value_intr.d  = chn1_val;

  //Connect the ports for future extension
  assign adc_chn_val_o[0].adc_chn_value_ext.de = 1'b0;
  assign adc_chn_val_o[0].adc_chn_value_ext.d  = 2'b0;
  assign adc_chn_val_o[1].adc_chn_value_ext.de = 1'b0;
  assign adc_chn_val_o[1].adc_chn_value_ext.d  = 2'b0;

  assign adc_chn_val_o[0].adc_chn_value_intr_ext.de = 1'b0;
  assign adc_chn_val_o[0].adc_chn_value_intr_ext.d  = 2'b0;
  assign adc_chn_val_o[1].adc_chn_value_intr_ext.de = 1'b0;
  assign adc_chn_val_o[1].adc_chn_value_intr_ext.d  = 2'b0;

  //Evaluate if there is a match from chn0 and chn1 samples
  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_match
    assign chn0_match[k] = (!aon_filter_ctl[0][k].cond) ?
            (aon_filter_ctl[0][k].min_v <= chn0_val) && (chn0_val <= aon_filter_ctl[0][k].max_v) :
            (aon_filter_ctl[0][k].min_v >  chn0_val) || (chn0_val >  aon_filter_ctl[0][k].max_v);
    assign chn1_match[k] = (!aon_filter_ctl[1][k].cond) ?
            (aon_filter_ctl[1][k].min_v <= chn1_val) && (chn1_val <= aon_filter_ctl[1][k].max_v) :
            (aon_filter_ctl[1][k].min_v >  chn1_val) || (chn1_val >  aon_filter_ctl[1][k].max_v);

    // If the filter on a paritcular channel is NOT enabled, it does not participate in the final
    // match decision.  This means the match value should have no impact on the final result.
    // For example, if channel 0's filter is enabled, but channel 1's is not, the match result
    // is determined solely based on whether channel 0's filter shows a match.
    // On the other hand, if all channel's filters are enabled, then a match is seen only when
    // both filters match.
    assign match[k] = |{aon_filter_ctl[0][k].en, aon_filter_ctl[1][k].en} &
                      (!aon_filter_ctl[0][k].en | (chn0_match[k] & aon_filter_ctl[0][k].en)) &
                      (!aon_filter_ctl[1][k].en | (chn1_match[k] & aon_filter_ctl[1][k].en)) ;

    assign match_pulse[k] = adc_ctrl_done && match[k];

   // Explicitly create assertions for all the matching conditions.
   // These assertions are unwieldly and not suitable for expansion to more channels.
   // They should be adjusted eventually.
   `ASSERT(MatchCheck00_A, !aon_filter_ctl[0][k].en & !aon_filter_ctl[1][k].en |->
           !match[k], clk_aon_i, !rst_aon_ni)
   `ASSERT(MatchCheck01_A, !aon_filter_ctl[0][k].en & aon_filter_ctl[1][k].en  |->
           match[k] == chn1_match[k], clk_aon_i, !rst_aon_ni)
   `ASSERT(MatchCheck10_A, aon_filter_ctl[0][k].en & !aon_filter_ctl[1][k].en  |->
           match[k] == chn0_match[k], clk_aon_i, !rst_aon_ni)
   `ASSERT(MatchCheck11_A, aon_filter_ctl[0][k].en & aon_filter_ctl[1][k].en   |->
           match[k] == (chn0_match[k] & chn1_match[k]), clk_aon_i, !rst_aon_ni)
  end

  // adc filter status
  assign aon_filter_status_o.d  = match_pulse | reg2hw_i.filter_status.q;
  assign aon_filter_status_o.de = |match_pulse;

  // generate wakeup to external power manager if filter status
  // and wakeup enable are set.
  assign wkup_req_o = |(reg2hw_i.filter_status.q &
                      reg2hw_i.adc_wakeup_ctl.q);

  //instantiate the main state machine
  adc_ctrl_fsm u_adc_ctrl_fsm (
    .clk_aon_i,
    .rst_aon_ni,
    // configuration and settings from reg interface
    .cfg_fsm_rst_i(reg2hw_i.adc_fsm_rst.q),
    .cfg_adc_enable_i(reg2hw_i.adc_en_ctl.adc_enable.q),
    .cfg_oneshot_mode_i(reg2hw_i.adc_en_ctl.oneshot_mode.q),
    .cfg_lp_mode_i(reg2hw_i.adc_pd_ctl.lp_mode.q),
    .cfg_pwrup_time_i(reg2hw_i.adc_pd_ctl.pwrup_time.q),
    .cfg_wakeup_time_i(reg2hw_i.adc_pd_ctl.wakeup_time.q),
    .cfg_lp_sample_cnt_i(reg2hw_i.adc_lp_sample_ctl.q),
    .cfg_np_sample_cnt_i(reg2hw_i.adc_sample_ctl.q),
    //
    .adc_ctrl_match_i(match),
    .adc_d_i(adc_i.data),
    .adc_d_val_i(adc_i.data_valid),
    .adc_pd_o(adc_o.pd),
    .adc_chn_sel_o(adc_o.channel_sel),
    .chn0_val_we_o(chn0_val_we),
    .chn1_val_we_o(chn1_val_we),
    .chn0_val_o(chn0_val),
    .chn1_val_o(chn1_val),
    .adc_ctrl_done_o(adc_ctrl_done),
    .oneshot_done_o(oneshot_done)
  );

  // synchronzie from clk_aon into cfg domain
  logic cfg_oneshot_done;
  prim_pulse_sync u_oneshot_done_sync (
    .clk_src_i(clk_aon_i),
    .rst_src_ni(rst_aon_ni),
    .src_pulse_i(oneshot_done),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(cfg_oneshot_done)
  );

  //Instantiate the interrupt module
  adc_ctrl_intr u_adc_ctrl_intr (
    .clk_aon_i,
    .rst_aon_ni,
    .aon_filter_match_i(match_pulse),
    .clk_i,
    .rst_ni,
    .cfg_intr_en_i(reg2hw_i.adc_intr_ctl.q),
    .cfg_oneshot_done_i(cfg_oneshot_done),
    .intr_state_i(reg2hw_i.intr_state),
    .intr_enable_i(reg2hw_i.intr_enable),
    .intr_test_i(reg2hw_i.intr_test),
    .intr_state_o,
    .adc_intr_status_i(reg2hw_i.adc_intr_status),
    .adc_intr_status_o,
    .intr_o
  );

  // unused register inputs
  logic unused_cfgs;
  assign unused_cfgs = ^reg2hw_i;

  //////////////////////
  // Assertions
  //////////////////////

  `ASSERT(MaxFilters_A, NumAdcFilter <= 32, clk_aon_i, !rst_aon_ni)

endmodule
