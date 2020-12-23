// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// DCD core module

module dcd_core (
  input clk_aon_i,//Always-on 200KHz clock(logic)
  input rst_slow_ni,//power-on reset for the 200KHz clock(logic)
  input clk_i,//regular core clock for SW config interface
  input rst_ni,//power-on hardware reset

  output debug_cable_wakeup,
  output intr_debug_cable_o,

  input  dcd_reg_pkg::dcd_reg2hw_t reg2hw,
  output dcd_reg_pkg::dcd_hw2reg_t hw2reg,

  input  ast_wrapper_pkg::adc_ast_rsp_t adc_i,
  output ast_wrapper_pkg::adc_ast_req_t adc_o
);

  import dcd_reg_pkg::* ;

  logic cfg_adc_enable;
  logic cfg_oneshot_mode;
  logic cfg_lp_mode;
  logic [3:0] cfg_pwrup_time;
  logic [23:0] cfg_wakeup_time;
  logic [7:0] cfg_lp_sample_cnt;
  logic [15:0] cfg_np_sample_cnt;
  logic cfg_fsm_rst;

  //There are eight filters
  //Each filter can have different settings
  logic [9:0] cfg_chn0_min_v [NumAdcFilter-1:0];
  logic [9:0] cfg_chn0_max_v [NumAdcFilter-1:0];
  logic [9:0] cfg_chn1_min_v [NumAdcFilter-1:0];
  logic [9:0] cfg_chn1_max_v [NumAdcFilter-1:0];
  logic [NumAdcFilter-1:0] cfg_chn0_cond;
  logic [NumAdcFilter-1:0] cfg_chn1_cond;

  //wakeup and interrupt control registers
  logic [NumAdcFilter-1:0] cfg_wakeup_en;
  //[0-7] for filters, [8] is for oneshot
  logic [NumAdcFilter-1:0] cfg_intr_en;
  logic cfg_oneshot_intr_en;

  logic chn0_val_we, chn1_val_we;//write enable for the latest ADC sample
  logic cfg_chn0_val_we, cfg_chn1_val_we;//CFG clock domain synchronized write enable for the latest ADC sample
  logic chn0_val_wready, chn1_val_wready;
  logic cfg_chn0_rvalid, cfg_chn1_rvalid;
  logic [9:0] chn0_val, chn1_val;
  logic [9:0] cfg_chn0_val, cfg_chn1_val;

  logic [NumAdcFilter-1:0] chn0_match, chn1_match, dcd_match;
  logic [NumAdcFilter-1:0] dcd_match_pulse;
  logic dcd_done, oneshot_done;//write enable for the ADC sample when the interrupt is triggered
  logic cfg_dcd_done, cfg_oneshot_done;//CFG clock domain synchronized write enable when interrupt is triggered
  logic cfg_chn_val_intr_we;//Either oneshot_done or dcd_done

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_adc_enable (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_en_ctl.adc_enable.q),
    .q(cfg_adc_enable)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_oneshot_mode (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_en_ctl.oneshot_mode.q),
    .q(cfg_oneshot_mode)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_lp_mode (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_pd_ctl.lp_mode.q),
    .q(cfg_lp_mode)
  );
  prim_fifo_async #(
    .Width(4),
    .Depth(1)
  ) i_cfg_pwrup_time (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_pd_ctl.pwrup_time.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_pd_ctl.pwrup_time.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_pwrup_time),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(24),
    .Depth(1)
  ) i_cfg_wakeup_time (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_pd_ctl.wakeup_time.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_pd_ctl.wakeup_time.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_wakeup_time),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(8),
    .Depth(1)
  ) i_cfg_lp_sample_cnt (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_lp_sample_ctl.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_lp_sample_ctl.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_lp_sample_cnt),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(16),
    .Depth(1)
  ) i_cfg_np_sample_cnt (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_sample_ctl.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_sample_ctl.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_np_sample_cnt),
    .rdepth_o  ()
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_fsm_rst (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_fsm_rst.q),
    .q(cfg_fsm_rst)
  );

  //synchronize between cfg(24MHz) and always-on(200KHz) for the filters
  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_sync
    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_chn0_cond (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_chn0_filter_ctl[k].cond.q),
    .q(cfg_chn0_cond[k])
  );

    prim_flop_2sync # (
    .Width(1)
  ) i_cfg_chn1_cond (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_chn1_filter_ctl[k].cond.q),
    .q(cfg_chn1_cond[k])
  );

    prim_fifo_async #(
    .Width(10),
    .Depth(1)
  ) i_cfg_chn0_min_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_chn0_filter_ctl[k].min_v.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_chn0_filter_ctl[k].min_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn0_min_v[k]),
    .rdepth_o  ()
  );

    prim_fifo_async #(
    .Width(10),
    .Depth(1)
  ) i_cfg_chn1_min_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_chn1_filter_ctl[k].min_v.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_chn1_filter_ctl[k].min_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn1_min_v[k]),
    .rdepth_o  ()
  );

    prim_fifo_async #(
    .Width(10),
    .Depth(1)
  ) i_cfg_chn0_max_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_chn0_filter_ctl[k].max_v.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_chn0_filter_ctl[k].max_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn0_max_v[k]),
    .rdepth_o  ()
  );

    prim_fifo_async #(
    .Width(10),
    .Depth(1)
  ) i_cfg_chn1_max_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.adc_chn1_filter_ctl[k].max_v.qe),
    .wready_o  (),
    .wdata_i   (reg2hw.adc_chn1_filter_ctl[k].max_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn1_max_v[k]),
    .rdepth_o  ()
  );
  end

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en0 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter0_en.q),
    .q(cfg_wakeup_en[0])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en1 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter1_en.q),
    .q(cfg_wakeup_en[1])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en2 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter2_en.q),
    .q(cfg_wakeup_en[2])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en3 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter3_en.q),
    .q(cfg_wakeup_en[3])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en4 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter4_en.q),
    .q(cfg_wakeup_en[4])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en5 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter5_en.q),
    .q(cfg_wakeup_en[5])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en6 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter6_en.q),
    .q(cfg_wakeup_en[6])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en7 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_wakeup_ctl.chn0_1_filter7_en.q),
    .q(cfg_wakeup_en[7])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en0 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter0_en.q),
    .q(cfg_intr_en[0])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en1 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter1_en.q),
    .q(cfg_intr_en[1])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en2 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter2_en.q),
    .q(cfg_intr_en[2])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en3 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter3_en.q),
    .q(cfg_intr_en[3])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en4 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter4_en.q),
    .q(cfg_intr_en[4])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en5 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter5_en.q),
    .q(cfg_intr_en[5])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en6 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter6_en.q),
    .q(cfg_intr_en[6])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en7 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.chn0_1_filter7_en.q),
    .q(cfg_intr_en[7])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_oneshot_intr_en (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d(reg2hw.adc_intr_ctl.oneshot_intr_en.q),
    .q(cfg_oneshot_intr_en)
  );

  //Synchronize from 200KHz always-onclock to 24MHz cfg clock
  prim_pulse_sync i_chn0_val_we (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (chn0_val_we),
    .dst_pulse_o (cfg_chn0_val_we)
  );

  prim_pulse_sync i_chn1_val_we (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (chn1_val_we),
    .dst_pulse_o (cfg_chn1_val_we)
  );

  prim_pulse_sync i_oneshot_done (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (oneshot_done),
    .dst_pulse_o (cfg_oneshot_done)
  );

  prim_pulse_sync i_dcd_done (
    .clk_src_i   (clk_aon_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_slow_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (dcd_done),
    .dst_pulse_o (cfg_dcd_done)
  );

  prim_fifo_async #(
    .Width(10),
    .Depth(1)
  ) i_cfg_chn0_val (
    .clk_wr_i  (clk_aon_i),
    .rst_wr_ni (rst_slow_ni),
    .wvalid_i  (chn0_val_we),
    .wready_o  (chn0_val_wready),
    .wdata_i   (chn0_val),
    .wdepth_o  (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (cfg_chn0_rvalid),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn0_val),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(10),
    .Depth(1)
  ) i_cfg_chn1_val (
    .clk_wr_i  (clk_aon_i),
    .rst_wr_ni (rst_slow_ni),
    .wvalid_i  (chn1_val_we),
    .wready_o  (chn1_val_wready),
    .wdata_i   (chn1_val),
    .wdepth_o  (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (cfg_chn1_rvalid),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn1_val),
    .rdepth_o  ()
  );

  //To write into adc_chn_val register
  assign hw2reg.adc_chn_val[0].adc_chn_value.de = cfg_chn0_val_we & cfg_chn0_rvalid;
  assign hw2reg.adc_chn_val[0].adc_chn_value.d = cfg_chn0_val;
  assign hw2reg.adc_chn_val[1].adc_chn_value.de = cfg_chn1_val_we & cfg_chn1_rvalid;
  assign hw2reg.adc_chn_val[1].adc_chn_value.d = cfg_chn1_val;

  assign cfg_chn_val_intr_we = cfg_oneshot_done || cfg_dcd_done;

  assign hw2reg.adc_chn_val[0].adc_chn_value_intr.de = cfg_chn_val_intr_we & cfg_chn0_rvalid;
  assign hw2reg.adc_chn_val[0].adc_chn_value_intr.d = cfg_chn0_val;
  assign hw2reg.adc_chn_val[1].adc_chn_value_intr.de = cfg_chn_val_intr_we & cfg_chn1_rvalid;
  assign hw2reg.adc_chn_val[1].adc_chn_value_intr.d = cfg_chn1_val;

  //Evaluate if there is a match from chn0 and chn1 samples
  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_match
    assign chn0_match[k] = (!cfg_chn0_cond[k]) ? (cfg_chn0_min_v[k] <= chn0_val) && (chn0_val <= cfg_chn0_max_v[k]) :
	    (cfg_chn0_min_v[k] > chn0_val) || (chn0_val > cfg_chn0_max_v[k]);
    assign chn1_match[k] = (!cfg_chn1_cond[k]) ? (cfg_chn1_min_v[k] <= chn1_val) && (chn1_val <= cfg_chn1_max_v[k]) :
	    (cfg_chn1_min_v[k] > chn1_val) || (chn1_val > cfg_chn1_max_v[k]);
    assign dcd_match[k] = chn0_match[k] && chn1_match[k];
    assign dcd_match_pulse[k] = dcd_done && dcd_match[k];
  end

  //instantiate the main state machine
  dcd_fsm i_dcd_fsm (
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .cfg_fsm_rst(cfg_fsm_rst),
    .cfg_adc_enable(cfg_adc_enable),
    .cfg_oneshot_mode(cfg_oneshot_mode),
    .cfg_lp_mode(cfg_lp_mode),
    .cfg_pwrup_time(cfg_pwrup_time),
    .cfg_wakeup_time(cfg_wakeup_time),
    .cfg_lp_sample_cnt(cfg_lp_sample_cnt),
    .cfg_np_sample_cnt(cfg_np_sample_cnt),
    .dcd_match(dcd_match),
    .adc_d(adc_i.data),
    .adc_d_val(adc_i.data_valid),
    .adc_pd(adc_o.pd),
    .adc_chn_sel(adc_o.channel_sel),
    .chn0_val_we(chn0_val_we),
    .chn1_val_we(chn1_val_we),
    .chn0_val(chn0_val),
    .chn1_val(chn1_val),
    .dcd_done(dcd_done),
    .oneshot_done(oneshot_done)
  );

  //Instantiate the interrupt module
  dcd_intr i_dcd_intr (
    .reg2hw(reg2hw),
    .hw2reg(hw2reg),
    .cfg_wakeup_en(cfg_wakeup_en),
    .cfg_intr_en(cfg_intr_en),
    .cfg_oneshot_intr_en(cfg_oneshot_intr_en),
    .dcd_match_pulse(dcd_match_pulse),
    .cfg_oneshot_done(cfg_oneshot_done),
    .debug_cable_wakeup(debug_cable_wakeup),
    .intr_debug_cable_o(intr_debug_cable_o)
  );


endmodule
