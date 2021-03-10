// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// DCD core module

module dcd_core import dcd_reg_pkg::* ; (
  input  clk_aon_i,//Always-on 200KHz clock(logic)
  input  rst_slow_ni,//power-on reset for the 200KHz clock(logic)
  input  clk_i,//regular core clock for SW config interface
  input  rst_ni,//power-on hardware reset

  input  dcd_reg2hw_adc_en_ctl_reg_t adc_en_ctl_i,
  input  dcd_reg2hw_adc_pd_ctl_reg_t adc_pd_ctl_i,
  input  dcd_reg2hw_adc_lp_sample_ctl_reg_t adc_lp_sample_ctl_i,
  input  dcd_reg2hw_adc_sample_ctl_reg_t adc_sample_ctl_i,
  input  dcd_reg2hw_adc_fsm_rst_reg_t adc_fsm_rst_i,
  input  dcd_reg2hw_adc_chn0_filter_ctl_mreg_t [NumAdcFilter-1:0] adc_chn0_filter_ctl_i,
  input  dcd_reg2hw_adc_chn1_filter_ctl_mreg_t [NumAdcFilter-1:0] adc_chn1_filter_ctl_i,
  input  dcd_reg2hw_adc_wakeup_ctl_reg_t adc_wakeup_ctl_i,
  input  dcd_reg2hw_adc_intr_ctl_reg_t adc_intr_ctl_i,

  output dcd_hw2reg_adc_chn_val_mreg_t [NumAdcChannel-1:0] adc_chn_val_o,

  input  dcd_reg2hw_intr_state_reg_t intr_state_i,
  input  dcd_reg2hw_intr_enable_reg_t intr_enable_i,
  input  dcd_reg2hw_intr_test_reg_t intr_test_i,

  output dcd_hw2reg_intr_state_reg_t intr_state_o,
  output dcd_hw2reg_adc_intr_status_reg_t adc_intr_status_o,
  output dcd_hw2reg_adc_wakeup_status_reg_t adc_wakeup_status_o,

  output debug_cable_wakeup_o,
  output intr_debug_cable_o,

  input  ast_pkg::adc_ast_rsp_t adc_i,
  output ast_pkg::adc_ast_req_t adc_o
);

  logic cfg_adc_enable;
  logic cfg_oneshot_mode;
  logic cfg_lp_mode;
  logic load_pwrup_time, load_wakeup_time;
  logic load_lp_sample_cnt, load_np_sample_cnt;
  logic [3:0] cfg_pwrup_time, cfg_pwrup_time_d;
  logic [23:0] cfg_wakeup_time, cfg_wakeup_time_d;
  logic [7:0] cfg_lp_sample_cnt, cfg_lp_sample_cnt_d;
  logic [15:0] cfg_np_sample_cnt, cfg_np_sample_cnt_d;
  logic cfg_fsm_rst;

  //There are eight filters
  //Each filter can have different settings
  logic [9:0] cfg_chn0_min_v [NumAdcFilter];
  logic [9:0] cfg_chn0_max_v [NumAdcFilter];
  logic [9:0] cfg_chn1_min_v [NumAdcFilter];
  logic [9:0] cfg_chn1_max_v [NumAdcFilter];
  logic [9:0] cfg_chn0_min_v_d [NumAdcFilter];
  logic [9:0] cfg_chn0_max_v_d [NumAdcFilter];
  logic [9:0] cfg_chn1_min_v_d [NumAdcFilter];
  logic [9:0] cfg_chn1_max_v_d [NumAdcFilter];
  logic [NumAdcFilter-1:0] cfg_chn0_cond;
  logic [NumAdcFilter-1:0] cfg_chn1_cond;
  logic [NumAdcFilter-1:0] load_chn0_min_v;
  logic [NumAdcFilter-1:0] load_chn1_min_v;
  logic [NumAdcFilter-1:0] load_chn0_max_v;
  logic [NumAdcFilter-1:0] load_chn1_max_v;

  //wakeup and interrupt control registers
  logic [NumAdcFilter-1:0] cfg_wakeup_en;
  //[0-7] for filters, [8] is for oneshot
  logic [NumAdcFilter-1:0] cfg_intr_en;
  logic cfg_oneshot_intr_en;

  logic chn0_val_we, chn1_val_we;//write enable for the latest ADC sample
  logic [9:0] chn0_val, chn1_val;
  logic cfg_chn0_rvalid, cfg_chn1_rvalid;
  logic [9:0] cfg_chn0_val, cfg_chn1_val;
  logic cfg_chn0_rvalid_intr, cfg_chn1_rvalid_intr;
  logic [9:0] cfg_chn0_val_intr, cfg_chn1_val_intr;

  logic [NumAdcFilter-1:0] chn0_match, chn1_match, dcd_match;
  logic [NumAdcFilter-1:0] dcd_match_pulse;
  logic dcd_done, oneshot_done;//write enable for the ADC sample when the interrupt is triggered
  logic cfg_dcd_done, cfg_oneshot_done;
  //CFG clock domain synchronized write enable when interrupt is triggered
  logic cfg_chn_val_intr_we;//Either oneshot_done or dcd_done

  //synchronize between cfg(24MHz) and always-on(200KHz)
  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_adc_enable (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_en_ctl_i.adc_enable.q),
    .q_o(cfg_adc_enable)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_oneshot_mode (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_en_ctl_i.oneshot_mode.q),
    .q_o(cfg_oneshot_mode)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_lp_mode (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_pd_ctl_i.lp_mode.q),
    .q_o(cfg_lp_mode)
  );
  prim_fifo_async #(
    .Width(4),
    .Depth(4)
  ) i_cfg_pwrup_time (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_pd_ctl_i.pwrup_time.qe),
    .wready_o  (),
    .wdata_i   (adc_pd_ctl_i.pwrup_time.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_pwrup_time),
    .rready_i  (1'b1),
    .rdata_o   (cfg_pwrup_time_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_pwrup_time_reg
    if (!rst_slow_ni) begin
      cfg_pwrup_time    <= '0;
    end else if (load_pwrup_time) begin
      cfg_pwrup_time    <= cfg_pwrup_time_d;
    end
  end

  prim_fifo_async #(
    .Width(24),
    .Depth(4)
  ) i_cfg_wakeup_time (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_pd_ctl_i.wakeup_time.qe),
    .wready_o  (),
    .wdata_i   (adc_pd_ctl_i.wakeup_time.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_wakeup_time),
    .rready_i  (1'b1),
    .rdata_o   (cfg_wakeup_time_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_wakeup_time_reg
    if (!rst_slow_ni) begin
      cfg_wakeup_time    <= '0;
    end else if (load_wakeup_time) begin
      cfg_wakeup_time    <= cfg_wakeup_time_d;
    end
  end

  prim_fifo_async #(
    .Width(8),
    .Depth(4)
  ) i_cfg_lp_sample_cnt (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_lp_sample_ctl_i.qe),
    .wready_o  (),
    .wdata_i   (adc_lp_sample_ctl_i.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_lp_sample_cnt),
    .rready_i  (1'b1),
    .rdata_o   (cfg_lp_sample_cnt_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_lp_sample_cnt_reg
    if (!rst_slow_ni) begin
      cfg_lp_sample_cnt    <= '0;
    end else if (load_lp_sample_cnt) begin
      cfg_lp_sample_cnt    <= cfg_lp_sample_cnt_d;
    end
  end

  prim_fifo_async #(
    .Width(16),
    .Depth(4)
  ) i_cfg_np_sample_cnt (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_sample_ctl_i.qe),
    .wready_o  (),
    .wdata_i   (adc_sample_ctl_i.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_np_sample_cnt),
    .rready_i  (1'b1),
    .rdata_o   (cfg_np_sample_cnt_d),
    .rdepth_o  ()
  );

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_np_sample_cnt_reg
    if (!rst_slow_ni) begin
      cfg_np_sample_cnt    <= '0;
    end else if (load_np_sample_cnt) begin
      cfg_np_sample_cnt    <= cfg_np_sample_cnt_d;
    end
  end

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_fsm_rst (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_fsm_rst_i.q),
    .q_o(cfg_fsm_rst)
  );

  //synchronize between cfg(24MHz) and always-on(200KHz) for the filters
  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_sync
    prim_flop_2sync # (
    .Width(1)
    ) i_cfg_chn0_cond (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_chn0_filter_ctl_i[k].cond.q),
    .q_o(cfg_chn0_cond[k])
    );

    prim_flop_2sync # (
    .Width(1)
    ) i_cfg_chn1_cond (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_chn1_filter_ctl_i[k].cond.q),
    .q_o(cfg_chn1_cond[k])
    );

    prim_fifo_async #(
    .Width(10),
    .Depth(4)
    ) i_cfg_chn0_min_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_chn0_filter_ctl_i[k].min_v.qe),
    .wready_o  (),
    .wdata_i   (adc_chn0_filter_ctl_i[k].min_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_chn0_min_v[k]),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn0_min_v_d[k]),
    .rdepth_o  ()
    );

    always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_chn0_min_v_reg
      if (!rst_slow_ni) begin
        cfg_chn0_min_v[k]    <= '0;
      end else if (load_chn0_min_v[k]) begin
        cfg_chn0_min_v[k]    <= cfg_chn0_min_v_d[k];
      end
    end


    prim_fifo_async #(
    .Width(10),
    .Depth(4)
    ) i_cfg_chn1_min_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_chn1_filter_ctl_i[k].min_v.qe),
    .wready_o  (),
    .wdata_i   (adc_chn1_filter_ctl_i[k].min_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_chn1_min_v[k]),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn1_min_v_d[k]),
    .rdepth_o  ()
    );

    always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_chn1_min_v_reg
      if (!rst_slow_ni) begin
        cfg_chn1_min_v[k]    <= '0;
      end else if (load_chn1_min_v[k]) begin
        cfg_chn1_min_v[k]    <= cfg_chn1_min_v_d[k];
      end
    end

    prim_fifo_async #(
    .Width(10),
    .Depth(4)
    ) i_cfg_chn0_max_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_chn0_filter_ctl_i[k].max_v.qe),
    .wready_o  (),
    .wdata_i   (adc_chn0_filter_ctl_i[k].max_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_chn0_max_v[k]),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn0_max_v_d[k]),
    .rdepth_o  ()
    );

    always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_chn0_max_v_reg
      if (!rst_slow_ni) begin
        cfg_chn0_max_v[k]    <= '0;
      end else if (load_chn0_max_v[k]) begin
        cfg_chn0_max_v[k]    <= cfg_chn0_max_v_d[k];
      end
    end

    prim_fifo_async #(
    .Width(10),
    .Depth(4)
    ) i_cfg_chn1_max_v (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (adc_chn1_filter_ctl_i[k].max_v.qe),
    .wready_o  (),
    .wdata_i   (adc_chn1_filter_ctl_i[k].max_v.q),
    .wdepth_o  (),

    .clk_rd_i  (clk_aon_i),
    .rst_rd_ni (rst_slow_ni),
    .rvalid_o  (load_chn1_max_v[k]),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn1_max_v_d[k]),
    .rdepth_o  ()
    );

    always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_cfg_chn1_max_v_reg
      if (!rst_slow_ni) begin
        cfg_chn1_max_v[k]    <= '0;
      end else if (load_chn1_max_v[k]) begin
        cfg_chn1_max_v[k]    <= cfg_chn1_max_v_d[k];
      end
    end

  end

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en0 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter0_en.q),
    .q_o(cfg_wakeup_en[0])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en1 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter1_en.q),
    .q_o(cfg_wakeup_en[1])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en2 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter2_en.q),
    .q_o(cfg_wakeup_en[2])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en3 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter3_en.q),
    .q_o(cfg_wakeup_en[3])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en4 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter4_en.q),
    .q_o(cfg_wakeup_en[4])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en5 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter5_en.q),
    .q_o(cfg_wakeup_en[5])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en6 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter6_en.q),
    .q_o(cfg_wakeup_en[6])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_wakeup_en7 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_wakeup_ctl_i.chn0_1_filter7_en.q),
    .q_o(cfg_wakeup_en[7])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en0 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter0_en.q),
    .q_o(cfg_intr_en[0])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en1 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter1_en.q),
    .q_o(cfg_intr_en[1])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en2 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter2_en.q),
    .q_o(cfg_intr_en[2])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en3 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter3_en.q),
    .q_o(cfg_intr_en[3])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en4 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter4_en.q),
    .q_o(cfg_intr_en[4])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en5 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter5_en.q),
    .q_o(cfg_intr_en[5])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en6 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter6_en.q),
    .q_o(cfg_intr_en[6])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_intr_en7 (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.chn0_1_filter7_en.q),
    .q_o(cfg_intr_en[7])
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_cfg_oneshot_intr_en (
    .clk_i(clk_aon_i),
    .rst_ni(rst_slow_ni),
    .d_i(adc_intr_ctl_i.oneshot_intr_en.q),
    .q_o(cfg_oneshot_intr_en)
  );

  //Synchronize from 200KHz always-onclock to 24MHz cfg clock
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
    .Depth(4)
  ) i_cfg_chn0_val (
    .clk_wr_i  (clk_aon_i),
    .rst_wr_ni (rst_slow_ni),
    .wvalid_i  (chn0_val_we),
    .wready_o  (),
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
    .Depth(4)
  ) i_cfg_chn1_val (
    .clk_wr_i  (clk_aon_i),
    .rst_wr_ni (rst_slow_ni),
    .wvalid_i  (chn1_val_we),
    .wready_o  (),
    .wdata_i   (chn1_val),
    .wdepth_o  (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (cfg_chn1_rvalid),
    .rready_i  (1'b1),
    .rdata_o   (cfg_chn1_val),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(10),
    .Depth(4)
  ) i_cfg_chn0_val_intr (
    .clk_wr_i  (clk_aon_i),
    .rst_wr_ni (rst_slow_ni),
    .wvalid_i  (chn0_val_we),
    .wready_o  (),
    .wdata_i   (chn0_val),
    .wdepth_o  (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (cfg_chn0_rvalid_intr),
    .rready_i  (cfg_chn_val_intr_we),
    .rdata_o   (cfg_chn0_val_intr),
    .rdepth_o  ()
  );

  prim_fifo_async #(
    .Width(10),
    .Depth(4)
  ) i_cfg_chn1_val_intr (
    .clk_wr_i  (clk_aon_i),
    .rst_wr_ni (rst_slow_ni),
    .wvalid_i  (chn1_val_we),
    .wready_o  (),
    .wdata_i   (chn1_val),
    .wdepth_o  (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (cfg_chn1_rvalid_intr),
    .rready_i  (cfg_chn_val_intr_we),
    .rdata_o   (cfg_chn1_val_intr),
    .rdepth_o  ()
  );
  //To write into adc_chn_val register
  assign adc_chn_val_o[0].adc_chn_value.de = cfg_chn0_rvalid;
  assign adc_chn_val_o[0].adc_chn_value.d = cfg_chn0_val;
  assign adc_chn_val_o[1].adc_chn_value.de = cfg_chn1_rvalid;
  assign adc_chn_val_o[1].adc_chn_value.d = cfg_chn1_val;

  assign cfg_chn_val_intr_we = cfg_oneshot_done || cfg_dcd_done;

  assign adc_chn_val_o[0].adc_chn_value_intr.de = cfg_chn0_rvalid_intr;
  assign adc_chn_val_o[0].adc_chn_value_intr.d = cfg_chn0_val_intr;
  assign adc_chn_val_o[1].adc_chn_value_intr.de = cfg_chn1_rvalid_intr;
  assign adc_chn_val_o[1].adc_chn_value_intr.d = cfg_chn1_val_intr;

  //Connect the ports for future extension
  assign adc_chn_val_o[0].adc_chn_value_ext.de = 1'b0;
  assign adc_chn_val_o[0].adc_chn_value_ext.d = 2'b0;
  assign adc_chn_val_o[1].adc_chn_value_ext.de = 1'b0;
  assign adc_chn_val_o[1].adc_chn_value_ext.d = 2'b0;

  assign adc_chn_val_o[0].adc_chn_value_intr_ext.de = 1'b0;
  assign adc_chn_val_o[0].adc_chn_value_intr_ext.d = 2'b0;
  assign adc_chn_val_o[1].adc_chn_value_intr_ext.de = 1'b0;
  assign adc_chn_val_o[1].adc_chn_value_intr_ext.d = 2'b0;

  //Evaluate if there is a match from chn0 and chn1 samples
  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_filter_match
    assign chn0_match[k] = (!cfg_chn0_cond[k]) ?
            (cfg_chn0_min_v[k] <= chn0_val) && (chn0_val <= cfg_chn0_max_v[k]) :
            (cfg_chn0_min_v[k] > chn0_val) || (chn0_val > cfg_chn0_max_v[k]);
    assign chn1_match[k] = (!cfg_chn1_cond[k]) ?
            (cfg_chn1_min_v[k] <= chn1_val) && (chn1_val <= cfg_chn1_max_v[k]) :
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
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .clk_aon_i(clk_aon_i),
    .rst_slow_ni(rst_slow_ni),
    .cfg_wakeup_en(cfg_wakeup_en),
    .cfg_intr_en(cfg_intr_en),
    .cfg_oneshot_intr_en(cfg_oneshot_intr_en),
    .dcd_match_pulse(dcd_match_pulse),
    .cfg_oneshot_done(cfg_oneshot_done),
    .intr_state_i(intr_state_i),
    .intr_enable_i(intr_enable_i),
    .intr_test_i(intr_test_i),
    .intr_state_o(intr_state_o),
    .adc_intr_status_o(adc_intr_status_o),
    .adc_wakeup_status_o(adc_wakeup_status_o),
    .debug_cable_wakeup_o(debug_cable_wakeup_o),
    .intr_debug_cable_o(intr_debug_cable_o)
  );


endmodule
