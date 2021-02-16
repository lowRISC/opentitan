// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description DCD detection FSM module

module dcd_fsm
  import dcd_reg_pkg::*;
(
  input clk_aon_i,
  input rst_slow_ni,
  input cfg_fsm_rst,
  input cfg_adc_enable,
  input cfg_oneshot_mode,
  input cfg_lp_mode,
  input [3:0] cfg_pwrup_time,
  input [23:0] cfg_wakeup_time,
  input [7:0]  cfg_lp_sample_cnt,
  input [15:0] cfg_np_sample_cnt,
  input [NumAdcFilter-1:0] dcd_match,
  input [9:0] adc_d,
  input       adc_d_val,//valid bit for ADC value
  output logic      adc_pd,
  output logic[1:0] adc_chn_sel,
  output logic      chn0_val_we,
  output logic      chn1_val_we,
  output logic [9:0] chn0_val,
  output logic [9:0] chn1_val,
  output logic       dcd_done,
  output logic       oneshot_done
);

  logic trigger_q;
  logic trigger_l2h, trigger_h2l;

  logic [3:0] pwrup_timer_cnt_d, pwrup_timer_cnt_q;
  logic pwrup_timer_cnt_clr, pwrup_timer_cnt_en;
  logic [9:0] chn0_val_d, chn1_val_d;
  logic fsm_chn0_sel, fsm_chn1_sel;
  logic chn0_val_we_d, chn1_val_we_d;
  logic [7:0] lp_sample_cnt_d, lp_sample_cnt_q;
  logic lp_sample_cnt_clr, lp_sample_cnt_en;
  logic [23:0] wakeup_timer_cnt_d, wakeup_timer_cnt_q;
  logic wakeup_timer_cnt_clr, wakeup_timer_cnt_en;
  logic [NumAdcFilter-1:0] dcd_match_q, fst_lp_match;
  logic any_fst_lp_match, stay_match;
  logic [15:0] np_sample_cnt_d, np_sample_cnt_q;
  logic np_sample_cnt_clr, np_sample_cnt_en;

  //FSM flow
  //1. PWRDN->PWRUP->IDLE->ONEST_0->ONEST_021->ONEST_1->PWRDN
  //2. PWRDN->PWRUP->IDLE->LP_0->LP_021->LP_1->LP_EVAL->LP_SLP->LP_PWRUP->LP0->
  //   LP_021->LP_1->LP_EVAL->NP_0->NP_021->NP_1->NP_EVAL->NP_0...repeat
  //3. PWRDN->PWRUP->IDLE->NP_0->NP_021->NP_1->NP_EVAL->NP_0....repeat
  typedef enum logic [3:0] {
                            PWRDN = 4'h0,// in the power down state
                            PWRUP = 4'h1,// being powered up
                            IDLE = 4'h2,// powered up after the pwrup_timer
                            ONEST_0 = 4'h3,// in oneshot mode; sample channel0 value
                            ONEST_021 = 4'h4,// in oneshot mode; transition from chn0 to chn1
                            ONEST_1 = 4'h5,// in oneshot mode; sample channel1 value
                            LP_0 = 4'h6,// in low-power mode, sample channel0 value
                            LP_021 = 4'h7,// in low-power mode, transition from chn0 to chn1
                            LP_1 = 4'h8,// in low-power mode, sample channel1 value
                            LP_EVAL = 4'h9,// in low-power mode, evaluate if there is a match
                            LP_SLP = 4'ha,// in low-power mode, go to sleep
                            LP_PWRUP = 4'hb,// in low-power mode, being powered up
                            NP_0 = 4'hc,// in normal-power mode, sample channel0 value
                            NP_021 = 4'hd,// in normal-power mode, transition from chn0 to chn1
                            NP_1 = 4'he,// in normal-power mode, sample channel1 value
                            NP_EVAL = 4'hf// in normal-power mode, detection is done
                            } fsm_state_e;

  fsm_state_e fsm_state_q, fsm_state_d;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_trigger_reg
    if (!rst_slow_ni) begin
      trigger_q <= 1'b0;
    end
    else if (cfg_fsm_rst) begin
      trigger_q <= 1'b0;
    end else begin
      trigger_q  <= cfg_adc_enable;
    end
  end

  assign trigger_l2h = (trigger_q == 1'b0) && (cfg_adc_enable == 1'b1);
  assign trigger_h2l = (trigger_q == 1'b1) && (cfg_adc_enable == 1'b0);

  assign pwrup_timer_cnt_d = (pwrup_timer_cnt_en) ? pwrup_timer_cnt_q + 1'b1 : pwrup_timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_pwrup_timer_cnt_reg
    if (!rst_slow_ni) begin
      pwrup_timer_cnt_q    <= '0;
    end
    else if (pwrup_timer_cnt_clr || cfg_fsm_rst) begin
       pwrup_timer_cnt_q <= '0;
    end else begin
       pwrup_timer_cnt_q <= pwrup_timer_cnt_d;
    end
  end

  assign lp_sample_cnt_d = (lp_sample_cnt_en) ? lp_sample_cnt_q + 1'b1 : lp_sample_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_lp_sample_cnt_reg
    if (!rst_slow_ni) begin
      lp_sample_cnt_q    <= '0;
    end
    else if (lp_sample_cnt_clr || cfg_fsm_rst) begin
      lp_sample_cnt_q <= '0;
    end else begin
      lp_sample_cnt_q <= lp_sample_cnt_d;
    end
  end

  assign np_sample_cnt_d = (np_sample_cnt_en) ? np_sample_cnt_q + 1'b1 : np_sample_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_np_sample_cnt_reg
    if (!rst_slow_ni) begin
      np_sample_cnt_q    <= '0;
    end
    else if (np_sample_cnt_clr || cfg_fsm_rst) begin
      np_sample_cnt_q <= '0;
    end else begin
      np_sample_cnt_q <= np_sample_cnt_d;
    end
  end

  assign wakeup_timer_cnt_d = (wakeup_timer_cnt_en) ?
           wakeup_timer_cnt_q + 1'b1 : wakeup_timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_wakeup_timer_cnt_reg
    if (!rst_slow_ni) begin
      wakeup_timer_cnt_q    <= '0;
    end
    else if (wakeup_timer_cnt_clr || cfg_fsm_rst) begin
      wakeup_timer_cnt_q <= '0;
    end else begin
      wakeup_timer_cnt_q <= wakeup_timer_cnt_d;
    end
  end

  assign fsm_chn0_sel = (fsm_state_q == ONEST_0) || (fsm_state_q == LP_0) || (fsm_state_q == NP_0);
  assign chn0_val_we_d = fsm_chn0_sel && adc_d_val;//adc_d_val is a valid pulse
  assign chn0_val_d = (chn0_val_we_d) ? adc_d : chn0_val;

  assign fsm_chn1_sel = (fsm_state_q == ONEST_1) || (fsm_state_q == LP_1) || (fsm_state_q == NP_1);
  assign chn1_val_we_d = fsm_chn1_sel && adc_d_val;
  assign chn1_val_d = (chn1_val_we_d) ? adc_d : chn1_val;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_chn01_val_we_reg
    if (!rst_slow_ni) begin
      chn0_val_we    <= '0;
      chn1_val_we    <= '0;
      chn0_val       <= '0;
      chn1_val       <= '0;
    end
    else if (cfg_fsm_rst) begin
      chn0_val_we    <= '0;
      chn1_val_we    <= '0;
      chn0_val       <= '0;
      chn1_val       <= '0;
    end else begin
      chn0_val_we    <= chn0_val_we_d;
      chn1_val_we    <= chn1_val_we_d;
      chn0_val       <= chn0_val_d;
      chn1_val       <= chn1_val_d;
    end
  end

  for (genvar k = 0 ; k < NumAdcFilter ; k++) begin : gen_fst_lp_match
    assign fst_lp_match[k] =
    ((lp_sample_cnt_q == 8'd1) && (fsm_state_q == LP_EVAL)) ? dcd_match[k] : 1'b0;
  end

  assign any_fst_lp_match = |fst_lp_match;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_dcd_match_reg
    if (!rst_slow_ni) begin
        dcd_match_q  <= '0;
    end
    else if (cfg_fsm_rst) begin
        dcd_match_q  <= '0;
    end
    else if ((fsm_state_q == LP_EVAL) || (fsm_state_q == NP_EVAL)) begin
        dcd_match_q  <= dcd_match;
    end
  end

  assign stay_match = any_fst_lp_match || (dcd_match == dcd_match_q);

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_fsm_state_reg
    if (!rst_slow_ni) begin
      fsm_state_q    <= PWRDN;
    end
    else if (trigger_h2l || cfg_fsm_rst) begin
      fsm_state_q    <= PWRDN;
    end else begin
      fsm_state_q    <= fsm_state_d;
    end
  end

  always_comb begin: adc_fsm
    fsm_state_d = fsm_state_q;
    //outputs
    adc_chn_sel = 2'b0;
    adc_pd = 1'b1;//default value
    pwrup_timer_cnt_clr = 1'b0;
    pwrup_timer_cnt_en = 1'b0;
    lp_sample_cnt_clr = 1'b0;
    lp_sample_cnt_en = 1'b0;
    wakeup_timer_cnt_clr = 1'b0;
    wakeup_timer_cnt_en = 1'b0;
    np_sample_cnt_clr = 1'b0;
    np_sample_cnt_en = 1'b0;
    dcd_done = 1'b0;
    oneshot_done = 1'b0;

    unique case (fsm_state_q)
      PWRDN: begin
        if (trigger_l2h) begin
          fsm_state_d = PWRUP;
        end
      end

      PWRUP: begin
        adc_pd = 1'b0;
        if (pwrup_timer_cnt_q != cfg_pwrup_time) begin
          pwrup_timer_cnt_en = 1'b1;
        end
        else if (pwrup_timer_cnt_q == cfg_pwrup_time) begin
          pwrup_timer_cnt_clr = 1'b1;
          fsm_state_d = IDLE;
        end
      end

      IDLE: begin
        adc_pd = 1'b0;
        if (cfg_oneshot_mode) begin
          fsm_state_d = ONEST_0;
        end
        else if (cfg_lp_mode) begin
          fsm_state_d = LP_0;
        end
        else if (!cfg_lp_mode) begin
          fsm_state_d = NP_0;
        end
      end

      ONEST_0: begin
        adc_pd = 1'b0;
        adc_chn_sel = 2'b01;
        if (adc_d_val) begin//sample chn0 value
          fsm_state_d = ONEST_021;
        end
      end

      ONEST_021: begin//transition betwenn chn0 and chn1; adc_chn_sel=2'b0
        adc_pd = 1'b0;
        fsm_state_d = ONEST_1;
      end

      ONEST_1: begin
        adc_pd = 1'b0;
        adc_chn_sel = 2'b10;
        if (adc_d_val) begin//sample chn1 value
          oneshot_done = 1'b1;
          fsm_state_d = PWRDN;
        end
      end

      LP_0: begin
        adc_pd = 1'b0;
        adc_chn_sel = 2'b01;
        if (adc_d_val) begin//sample chn0 value
          fsm_state_d = LP_021;
        end
      end

      LP_021: begin//transition betwenn chn0 and chn1; adc_chn_sel=2'b0
        adc_pd = 1'b0;
        fsm_state_d = LP_1;
      end

      LP_1: begin
        adc_pd = 1'b0;
        adc_chn_sel = 2'b10;
        if (adc_d_val) begin//sample chn1 value
          fsm_state_d = LP_EVAL;
          lp_sample_cnt_en = 1'b1;
        end
      end

      LP_EVAL: begin
        adc_pd = 1'b0;
        if ((lp_sample_cnt_q != cfg_lp_sample_cnt) && (stay_match == 1'b1)) begin
          fsm_state_d = LP_SLP;
        end
        else if ((lp_sample_cnt_q != cfg_lp_sample_cnt) && (stay_match != 1'b1)) begin
          fsm_state_d = LP_SLP;
          lp_sample_cnt_clr = 1'b1;
        end
        else if ((lp_sample_cnt_q == cfg_lp_sample_cnt) && (stay_match == 1'b1)) begin
          fsm_state_d = NP_0;
          lp_sample_cnt_clr = 1'b1;
        end
      end

      LP_SLP: begin
        adc_pd = 1'b1;
        if (wakeup_timer_cnt_q  != cfg_wakeup_time) begin
          wakeup_timer_cnt_en = 1'b1;
        end
        else if (wakeup_timer_cnt_q == cfg_wakeup_time) begin
          fsm_state_d = LP_PWRUP;
          wakeup_timer_cnt_clr = 1'b1;
        end
      end

      LP_PWRUP: begin
        adc_pd = 1'b0;
        if (pwrup_timer_cnt_q != cfg_pwrup_time) begin
          pwrup_timer_cnt_en = 1'b1;
        end
        else if (pwrup_timer_cnt_q == cfg_pwrup_time) begin
          pwrup_timer_cnt_clr = 1'b1;
          fsm_state_d = LP_0;
        end
      end

      NP_0: begin
        adc_pd = 1'b0;
        adc_chn_sel = 2'b01;
        if (adc_d_val) begin//sample chn0 value
          fsm_state_d = NP_021;
        end
      end

      NP_021: begin//transition betwenn chn0 and chn1; adc_chn_sel=2'b0
        adc_pd = 1'b0;
        fsm_state_d = NP_1;
      end

      NP_1: begin
        adc_pd = 1'b0;
        adc_chn_sel = 2'b10;
        if (adc_d_val) begin//sample chn1 value
          fsm_state_d = NP_EVAL;
          np_sample_cnt_en = 1'b1;
        end
      end

      NP_EVAL: begin
        adc_pd = 1'b0;
        if ((np_sample_cnt_q != cfg_np_sample_cnt) && (stay_match == 1'b1)) begin
          fsm_state_d = NP_0;
        end
        else if ((np_sample_cnt_q != cfg_np_sample_cnt) && (stay_match != 1'b1)) begin
          fsm_state_d = NP_0;
          np_sample_cnt_clr = 1'b1;
        end
        else if ((np_sample_cnt_q == cfg_np_sample_cnt) && (stay_match == 1'b1)) begin
          fsm_state_d = NP_0;
          np_sample_cnt_clr = 1'b1;
          dcd_done = 1'b1;
        end
      end

      default: fsm_state_d = PWRDN;
    endcase
  end


endmodule
