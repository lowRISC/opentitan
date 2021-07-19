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
  input  adc_ctrl_reg2hw_adc_en_ctl_reg_t adc_en_ctl_i,
  input  adc_ctrl_reg2hw_adc_pd_ctl_reg_t adc_pd_ctl_i,
  input  adc_ctrl_reg2hw_adc_lp_sample_ctl_reg_t adc_lp_sample_ctl_i,
  input  adc_ctrl_reg2hw_adc_sample_ctl_reg_t adc_sample_ctl_i,
  input  adc_ctrl_reg2hw_adc_fsm_rst_reg_t adc_fsm_rst_i,
  input  adc_ctrl_reg2hw_adc_chn0_filter_ctl_mreg_t [NumAdcFilter-1:0] adc_chn0_filter_ctl_i,
  input  adc_ctrl_reg2hw_adc_chn1_filter_ctl_mreg_t [NumAdcFilter-1:0] adc_chn1_filter_ctl_i,
  input  adc_ctrl_reg2hw_adc_intr_ctl_reg_t adc_intr_ctl_i,
  input  adc_ctrl_reg2hw_adc_wakeup_ctl_reg_t adc_wakeup_ctl_i,
  input  adc_ctrl_reg2hw_adc_wakeup_status_reg_t adc_wakeup_status_i,

  output adc_ctrl_hw2reg_adc_chn_val_mreg_t [NumAdcChannel-1:0] adc_chn_val_o,

  input  adc_ctrl_reg2hw_intr_state_reg_t intr_state_i,
  input  adc_ctrl_reg2hw_intr_enable_reg_t intr_enable_i,
  input  adc_ctrl_reg2hw_intr_test_reg_t intr_test_i,

  output adc_ctrl_hw2reg_intr_state_reg_t intr_state_o,
  output adc_ctrl_hw2reg_adc_intr_status_reg_t adc_intr_status_o,
  output adc_ctrl_hw2reg_adc_wakeup_status_reg_t adc_wakeup_status_o,

  output debug_cable_wakeup_o,
  output intr_debug_cable_o,

  input  ast_pkg::adc_ast_rsp_t adc_i,
  output ast_pkg::adc_ast_req_t adc_o
);


  logic chn0_val_we, chn1_val_we;//write enable for the latest ADC sample
  logic [9:0] chn0_val, chn1_val;
  logic cfg_chn0_rvalid, cfg_chn1_rvalid;

  logic [NumAdcFilter-1:0] chn0_match, chn1_match, match;
  logic [NumAdcFilter-1:0] match_pulse;
  //write enable for the ADC sample when the interrupt is triggered
  logic adc_ctrl_done, oneshot_done;
  logic cfg_adc_ctrl_done, cfg_oneshot_done;
  //CFG clock domain synchronized write enable when interrupt is triggered
  logic cfg_chn_val_intr_we;//Either oneshot_done or adc_ctrl_done


  // tieoff unused signals
  logic [NumAdcFilter-1:0] unused_qe;
  logic unused_lp_mode_qe;
  for (genvar i=0; i < NumAdcFilter; i++) begin : gen_unused_tieoff
    assign unused_qe[i] = adc_chn0_filter_ctl_i[i].cond.qe ^
                          adc_chn0_filter_ctl_i[i].min_v.qe ^
                          adc_chn0_filter_ctl_i[i].max_v.qe ^
                          adc_chn1_filter_ctl_i[i].cond.qe ^
                          adc_chn1_filter_ctl_i[i].min_v.qe ^
                          adc_chn1_filter_ctl_i[i].max_v.qe;
  end

  assign unused_lp_mode_qe = adc_pd_ctl_i.lp_mode.qe;

  /////////////////////////////
  // Synchronize from cfg domain to aon domain
  /////////////////////////////
  logic [NumAdcFilter-1:0] aon_wakeup_en;
  logic aon_adc_enable;
  logic aon_oneshot_mode;
  logic aon_lp_mode;
  logic [3:0] aon_pwrup_time;
  logic [23:0] aon_wakeup_time;
  logic [7:0] aon_lp_sample_cnt;
  logic [15:0] aon_np_sample_cnt;
  logic aon_fsm_rst;

  //synchronize between cfg and always-on
  prim_flop_2sync # (
    .Width(1)
  ) u_cfg_adc_enable (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(adc_en_ctl_i.adc_enable.q),
    .q_o(aon_adc_enable)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_cfg_oneshot_mode (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(adc_en_ctl_i.oneshot_mode.q),
    .q_o(aon_oneshot_mode)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_cfg_lp_mode (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(adc_pd_ctl_i.lp_mode.q),
    .q_o(aon_lp_mode)
  );

  // all qe's for a register are the same
  logic adc_pd_ctl_qe;
  assign adc_pd_ctl_qe = adc_pd_ctl_i.pwrup_time.qe |
                         adc_pd_ctl_i.wakeup_time.qe;

  prim_pulse_sync_data #(
    .DataWidth(28)
  ) u_cfg_adc_pd_ctl (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .src_pulse_i(adc_pd_ctl_qe),
    .src_data_i({adc_pd_ctl_i.pwrup_time.q, adc_pd_ctl_i.wakeup_time.q}),
    .src_ack_pulse_o(),
    .clk_dst_i(clk_aon_i),
    .rst_dst_ni(rst_aon_ni),
    .dst_pulse_o(),
    .dst_data_o({aon_pwrup_time, aon_wakeup_time})
  );

  prim_pulse_sync_data #(
    .DataWidth(8)
  ) u_cfg_lp_sample_cnt (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .src_pulse_i(adc_lp_sample_ctl_i.qe),
    .src_data_i(adc_lp_sample_ctl_i.q),
    .src_ack_pulse_o(),
    .clk_dst_i(clk_aon_i),
    .rst_dst_ni(rst_aon_ni),
    .dst_pulse_o(),
    .dst_data_o(aon_lp_sample_cnt)
  );

  prim_pulse_sync_data #(
    .DataWidth(16)
  ) u_cfg_np_sample_cnt (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .src_pulse_i(adc_sample_ctl_i.qe),
    .src_data_i(adc_sample_ctl_i.q),
    .src_ack_pulse_o(),
    .clk_dst_i(clk_aon_i),
    .rst_dst_ni(rst_aon_ni),
    .dst_pulse_o(),
    .dst_data_o(aon_np_sample_cnt)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_cfg_fsm_rst (
    .clk_i(clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i(adc_fsm_rst_i.q),
    .q_o(aon_fsm_rst)
  );

  typedef struct packed {
    logic [9:0] min_v;
    logic [9:0] max_v;
    logic cond;
    logic en;
  } filter_ctl_t;
  localparam int FilterCtrlWidth = $bits(filter_ctl_t);

  filter_ctl_t [NumAdcChannel-1:0][NumAdcFilter-1:0] aon_filter_ctl;

  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_ctl_sync

    filter_ctl_t [NumAdcChannel-1:0] cfg_filter_ctl;

    assign cfg_filter_ctl[0] = '{
      min_v: adc_chn0_filter_ctl_i[k].min_v.q,
      max_v: adc_chn0_filter_ctl_i[k].max_v.q,
      cond:  adc_chn0_filter_ctl_i[k].cond.q,
      en:    adc_chn0_filter_ctl_i[k].en.q
    };

    assign cfg_filter_ctl[1] = '{
      min_v: adc_chn1_filter_ctl_i[k].min_v.q,
      max_v: adc_chn1_filter_ctl_i[k].max_v.q,
      cond:  adc_chn1_filter_ctl_i[k].cond.q,
      en:    adc_chn1_filter_ctl_i[k].en.q
    };

    prim_pulse_sync_data #(
      .DataWidth(FilterCtrlWidth)
    ) u_chn0_filter_ctl_sync (
      .clk_src_i(clk_i),
      .rst_src_ni(rst_ni),
      .src_pulse_i(adc_chn0_filter_ctl_i[k].en.qe),
      .src_data_i(cfg_filter_ctl[0]),
      .src_ack_pulse_o(),
      .clk_dst_i(clk_aon_i),
      .rst_dst_ni(rst_aon_ni),
      .dst_pulse_o(),
      .dst_data_o(aon_filter_ctl[0][k])
    );

    prim_pulse_sync_data #(
      .DataWidth(FilterCtrlWidth)
    ) u_chn1_filter_ctl_sync (
      .clk_src_i(clk_i),
      .rst_src_ni(rst_ni),
      .src_pulse_i(adc_chn1_filter_ctl_i[k].en.qe),
      .src_data_i(cfg_filter_ctl[1]),
      .src_ack_pulse_o(),
      .clk_dst_i(clk_aon_i),
      .rst_dst_ni(rst_aon_ni),
      .dst_pulse_o(),
      .dst_data_o(aon_filter_ctl[1][k])
    );
  end // block: gen_filter_ctl_sync


  logic aon_qe;
  prim_pulse_sync u_filter_status_qe_sync (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .src_pulse_i(adc_wakeup_status_i.qe),
    .clk_dst_i(clk_aon_i),
    .rst_dst_ni(rst_aon_ni),
    .dst_pulse_o(aon_qe)
  );

  // write-one to clear
  logic [NumAdcFilter-1:0] aon_wakeup_clr;
  assign aon_wakeup_clr = {NumAdcFilter{aon_qe}} & adc_wakeup_status_i.q;

  prim_pulse_sync_data #(
    .DataWidth(NumAdcFilter)
  ) u_wake_en_sync (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .src_pulse_i(adc_wakeup_ctl_i.qe),
    .src_data_i(adc_wakeup_ctl_i.q),
    .src_ack_pulse_o(),
    .clk_dst_i(clk_aon_i),
    .rst_dst_ni(rst_aon_ni),
    .dst_pulse_o(),
    .dst_data_o(aon_wakeup_en)
  );

  /////////////////////////////
  // Synchronize from aon domain to cfg domain
  /////////////////////////////
  prim_pulse_sync u_oneshot_done (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (oneshot_done),
    .dst_pulse_o (cfg_oneshot_done)
  );

  prim_pulse_sync u_adc_ctrl_done (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (adc_ctrl_done),
    .dst_pulse_o (cfg_adc_ctrl_done)
  );

  prim_pulse_sync u_cfg_chn0_val (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (chn0_val_we),
    .dst_pulse_o (cfg_chn0_rvalid)
  );

  prim_pulse_sync u_cfg_chn1_val (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_aon_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (chn1_val_we),
    .dst_pulse_o (cfg_chn1_rvalid)
  );

  //To write into adc_chn_val register
  assign adc_chn_val_o[0].adc_chn_value.de = cfg_chn0_rvalid;
  assign adc_chn_val_o[0].adc_chn_value.d  = chn0_val;
  assign adc_chn_val_o[1].adc_chn_value.de = cfg_chn1_rvalid;
  assign adc_chn_val_o[1].adc_chn_value.d  = chn1_val;

  // The value of the adc is captured whenever an interrupt triggers.
  // There are two cases:
  // completion of one shot mode
  // match detection from the filters
  assign cfg_chn_val_intr_we = adc_en_ctl_i.oneshot_mode.q ? cfg_oneshot_done  :
                               adc_en_ctl_i.adc_enable.q   ? cfg_adc_ctrl_done : '0;

  assign adc_chn_val_o[0].adc_chn_value_intr.de = cfg_chn_val_intr_we;
  assign adc_chn_val_o[0].adc_chn_value_intr.d  = chn0_val;
  assign adc_chn_val_o[1].adc_chn_value_intr.de = cfg_chn_val_intr_we;
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
            (aon_filter_ctl[1][k].min_v <= chn0_val) && (chn0_val <= aon_filter_ctl[1][k].max_v) :
            (aon_filter_ctl[1][k].min_v >  chn0_val) || (chn0_val >  aon_filter_ctl[1][k].max_v);

    assign match[k] = (chn0_match[k] & aon_filter_ctl[0][k].en) &
                      (chn1_match[k] & aon_filter_ctl[1][k].en);
    assign match_pulse[k] = adc_ctrl_done && match[k];
  end

  // Filter status
  logic [NumAdcFilter-1:0] aon_wakeup_status;
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      aon_wakeup_status <= '0;
    end else begin
      // if a match and clear happen at the same time, prioritize the match
      for(int i = 0; i < NumAdcFilter; i++) begin
        if (match_pulse[i]) begin
          aon_wakeup_status[i] <= 1'b1;
        end else if (aon_wakeup_clr[i]) begin
          aon_wakeup_status[i] <= 1'b0;
        end
      end
    end
  end

  // generate wakeup to external power manager
  assign debug_cable_wakeup_o = |(aon_wakeup_status & aon_wakeup_en);

  //instantiate the main state machine
  adc_ctrl_fsm u_adc_ctrl_fsm (
    .clk_aon_i,
    .rst_aon_ni,
    // configuration and settings from reg interface
    .cfg_fsm_rst_i(aon_fsm_rst),
    .cfg_adc_enable_i(aon_adc_enable),
    .cfg_oneshot_mode_i(aon_oneshot_mode),
    .cfg_lp_mode_i(aon_lp_mode),
    .cfg_pwrup_time_i(aon_pwrup_time),
    .cfg_wakeup_time_i(aon_wakeup_time),
    .cfg_lp_sample_cnt_i(aon_lp_sample_cnt),
    .cfg_np_sample_cnt_i(aon_np_sample_cnt),
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

  //Instantiate the interrupt module
  adc_ctrl_intr u_adc_ctrl_intr (
    .clk_i,
    .rst_ni,
    .adc_wakeup_status_i(adc_wakeup_status_i.q),
    .aon_filter_status_i(aon_wakeup_status),
    .cfg_intr_en_i(adc_intr_ctl_i),
    .cfg_oneshot_done_i(cfg_oneshot_done),
    .intr_state_i,
    .intr_enable_i,
    .intr_test_i,
    .intr_state_o,
    .adc_intr_status_o,
    .adc_wakeup_status_o,
    .intr_debug_cable_o
  );

  //////////////////////
  // Assertions
  //////////////////////

  `ASSERT_INIT(MaxFilters_A, NumAdcFilter <= 32)
  `ASSERT(OneHotMatch_A, adc_ctrl_done |-> $onehot0(match_pulse))

endmodule
