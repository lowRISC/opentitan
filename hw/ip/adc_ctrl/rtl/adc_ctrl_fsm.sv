// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description adc_ctrl detection FSM module

module adc_ctrl_fsm
  import adc_ctrl_reg_pkg::*;
  import adc_ctrl_pkg::*;
(
  input clk_aon_i,
  input rst_aon_ni,
  input cfg_fsm_rst_i,
  input cfg_adc_enable_i,
  input cfg_oneshot_mode_i,
  input cfg_lp_mode_i,
  input [3:0] cfg_pwrup_time_i,
  input [23:0] cfg_wakeup_time_i,
  input [7:0]  cfg_lp_sample_cnt_i,
  input [15:0] cfg_np_sample_cnt_i,
  input [NumAdcFilter-1:0] adc_ctrl_match_i,
  input [9:0] adc_d_i,
  input       adc_d_val_i,//valid bit for ADC value
  output logic      adc_pd_o,
  output logic[1:0] adc_chn_sel_o,
  output logic      chn0_val_we_o,
  output logic      chn1_val_we_o,
  output logic [9:0] chn0_val_o,
  output logic [9:0] chn1_val_o,
  output logic       adc_ctrl_done_o,
  output logic       oneshot_done_o
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
  logic [NumAdcFilter-1:0] adc_ctrl_match_q;
  logic stay_match;
  logic [15:0] np_sample_cnt_d, np_sample_cnt_q;
  logic np_sample_cnt_clr, np_sample_cnt_en;
  logic [7:0] lp_sample_cnt_thresh;
  logic [15:0] np_sample_cnt_thresh;


  fsm_state_e fsm_state_q, fsm_state_d;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      trigger_q <= 1'b0;
    end
    else if (cfg_fsm_rst_i) begin
      trigger_q <= 1'b0;
    end else begin
      trigger_q  <= cfg_adc_enable_i;
    end
  end

  assign trigger_l2h = (trigger_q == 1'b0) && (cfg_adc_enable_i == 1'b1);
  assign trigger_h2l = (trigger_q == 1'b1) && (cfg_adc_enable_i == 1'b0);

  assign pwrup_timer_cnt_d = (pwrup_timer_cnt_en) ? pwrup_timer_cnt_q + 1'b1 : pwrup_timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      pwrup_timer_cnt_q    <= '0;
    end
    else if (pwrup_timer_cnt_clr || cfg_fsm_rst_i || trigger_h2l) begin
       pwrup_timer_cnt_q <= '0;
    end else begin
       pwrup_timer_cnt_q <= pwrup_timer_cnt_d;
    end
  end

  assign lp_sample_cnt_d = (lp_sample_cnt_en) ? lp_sample_cnt_q + 1'b1 : lp_sample_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      lp_sample_cnt_q    <= '0;
    end
    else if (lp_sample_cnt_clr || cfg_fsm_rst_i || trigger_h2l) begin
      lp_sample_cnt_q <= '0;
    end else begin
      lp_sample_cnt_q <= lp_sample_cnt_d;
    end
  end

  assign np_sample_cnt_d = (np_sample_cnt_en) ? np_sample_cnt_q + 1'b1 : np_sample_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      np_sample_cnt_q    <= '0;
    end
    else if (np_sample_cnt_clr || cfg_fsm_rst_i || trigger_h2l) begin
      np_sample_cnt_q <= '0;
    end else begin
      np_sample_cnt_q <= np_sample_cnt_d;
    end
  end

  assign wakeup_timer_cnt_d = (wakeup_timer_cnt_en) ?
           wakeup_timer_cnt_q + 1'b1 : wakeup_timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wakeup_timer_cnt_q    <= '0;
    end
    else if (wakeup_timer_cnt_clr || cfg_fsm_rst_i || trigger_h2l) begin
      wakeup_timer_cnt_q <= '0;
    end else begin
      wakeup_timer_cnt_q <= wakeup_timer_cnt_d;
    end
  end

  assign fsm_chn0_sel = (fsm_state_q == ONEST_0) || (fsm_state_q == LP_0) || (fsm_state_q == NP_0);
  assign chn0_val_we_d = fsm_chn0_sel && adc_d_val_i;//adc_d_val_i is a valid pulse
  assign chn0_val_d = (chn0_val_we_d) ? adc_d_i : chn0_val_o;

  assign fsm_chn1_sel = (fsm_state_q == ONEST_1) || (fsm_state_q == LP_1) || (fsm_state_q == NP_1);
  assign chn1_val_we_d = fsm_chn1_sel && adc_d_val_i;
  assign chn1_val_d = (chn1_val_we_d) ? adc_d_i : chn1_val_o;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      chn0_val_we_o  <= '0;
      chn1_val_we_o  <= '0;
      chn0_val_o     <= '0;
      chn1_val_o     <= '0;
    end
    else if (cfg_fsm_rst_i) begin
      chn0_val_we_o  <= '0;
      chn1_val_we_o  <= '0;
      chn0_val_o     <= '0;
      chn1_val_o     <= '0;
    end else begin
      chn0_val_we_o  <= chn0_val_we_d;
      chn1_val_we_o  <= chn1_val_we_d;
      chn0_val_o     <= chn0_val_d;
      chn1_val_o     <= chn1_val_d;
    end
  end

  // TODO: #13725
  // The logic below can be enhanced for better handling in the future
  logic ld_match;
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
        adc_ctrl_match_q  <= '0;
    end
    else if (cfg_fsm_rst_i) begin
        adc_ctrl_match_q  <= '0;
    end
    else if (ld_match) begin
        adc_ctrl_match_q  <= adc_ctrl_match_i;
    end
  end

  logic np_match;
  assign np_match = |adc_ctrl_match_i &                       // if current match is non-zero
                    ((adc_ctrl_match_i == adc_ctrl_match_q) | // match if same as previous match
                    ~|adc_ctrl_match_q);                      // or match if previous match was zero

  assign stay_match = np_match;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      fsm_state_q    <= PWRDN;
    end
    else if (trigger_h2l || cfg_fsm_rst_i) begin
      fsm_state_q    <= PWRDN;
    end else begin
      fsm_state_q    <= fsm_state_d;
    end
  end

  assign lp_sample_cnt_thresh = cfg_lp_sample_cnt_i - 1'b1;
  assign np_sample_cnt_thresh = cfg_np_sample_cnt_i - 1'b1;


  always_comb begin: adc_fsm
    fsm_state_d = fsm_state_q;
    //outputs
    adc_chn_sel_o = 2'b0;
    adc_pd_o = 1'b0;//default value
    pwrup_timer_cnt_clr = 1'b0;
    pwrup_timer_cnt_en = 1'b0;
    lp_sample_cnt_clr = 1'b0;
    lp_sample_cnt_en = 1'b0;
    wakeup_timer_cnt_clr = 1'b0;
    wakeup_timer_cnt_en = 1'b0;
    np_sample_cnt_clr = 1'b0;
    np_sample_cnt_en = 1'b0;
    adc_ctrl_done_o = 1'b0;
    oneshot_done_o = 1'b0;
    ld_match = 1'b0;

    unique case (fsm_state_q)
      PWRDN: begin
        adc_pd_o = 1'b1;
        if (trigger_l2h) begin
          fsm_state_d = PWRUP;
        end
      end

      PWRUP: begin
        if (pwrup_timer_cnt_q != cfg_pwrup_time_i) begin
          pwrup_timer_cnt_en = 1'b1;
        end
        else if (pwrup_timer_cnt_q == cfg_pwrup_time_i) begin
          pwrup_timer_cnt_clr = 1'b1;
          if (cfg_oneshot_mode_i) begin
            fsm_state_d = ONEST_0;
          end
          else if (cfg_lp_mode_i) begin
            fsm_state_d = LP_0;
          end
          else if (!cfg_lp_mode_i) begin
            fsm_state_d = NP_0;
          end
        end
      end

      ONEST_0: begin
        adc_chn_sel_o = 2'b01;
        if (adc_d_val_i) begin//sample chn0 value
          fsm_state_d = ONEST_021;
        end
      end

      ONEST_021: begin//transition between chn0 and chn1; adc_chn_sel_o=2'b0
        if (!adc_d_val_i) begin
          fsm_state_d = ONEST_1;
        end
      end

      ONEST_1: begin
        adc_chn_sel_o = 2'b10;
        if (adc_d_val_i) begin//sample chn1 value
          fsm_state_d = ONEST_DONE;
        end
      end

      // delay done assertion by one cycle to match
      // adc capture register timing
      ONEST_DONE: begin
        oneshot_done_o = 1'b1;
        fsm_state_d = PWRDN;
      end

      LP_0: begin
        adc_chn_sel_o = 2'b01;
        if (adc_d_val_i) begin//sample chn0 value
          fsm_state_d = LP_021;
        end
      end

      LP_021: begin//transition between chn0 and chn1; adc_chn_sel_o=2'b0
        if (!adc_d_val_i) begin
          fsm_state_d = LP_1;
        end
      end

      LP_1: begin
        adc_chn_sel_o = 2'b10;
        if (adc_d_val_i) begin//sample chn1 value
          fsm_state_d = LP_EVAL;
        end
      end

      LP_EVAL: begin
        // do not transition forward until handshake with ADC is complete
        if (!adc_d_val_i) begin
          ld_match = 1'b1;
          if (!stay_match) begin
            fsm_state_d = LP_SLP;
            lp_sample_cnt_clr = 1'b1;
          end else if (lp_sample_cnt_q < lp_sample_cnt_thresh) begin
            fsm_state_d = LP_SLP;
            lp_sample_cnt_en = 1'b1;
          end else if (lp_sample_cnt_q == lp_sample_cnt_thresh) begin
            fsm_state_d = NP_0;
            lp_sample_cnt_clr = 1'b1;
          end
        end
      end

      LP_SLP: begin
        adc_pd_o = 1'b1;
        if (wakeup_timer_cnt_q  != cfg_wakeup_time_i) begin
          wakeup_timer_cnt_en = 1'b1;
        end
        else if (wakeup_timer_cnt_q == cfg_wakeup_time_i) begin
          fsm_state_d = LP_PWRUP;
          wakeup_timer_cnt_clr = 1'b1;
        end
      end

      LP_PWRUP: begin
        if (pwrup_timer_cnt_q != cfg_pwrup_time_i) begin
          pwrup_timer_cnt_en = 1'b1;
        end
        else if (pwrup_timer_cnt_q == cfg_pwrup_time_i) begin
          pwrup_timer_cnt_clr = 1'b1;
          fsm_state_d = LP_0;
        end
      end

      NP_0: begin
        adc_chn_sel_o = 2'b01;
        if (adc_d_val_i) begin//sample chn0 value
          fsm_state_d = NP_021;
        end
      end

      NP_021: begin//transition between chn0 and chn1; adc_chn_sel_o=2'b0
        if (!adc_d_val_i) begin
          fsm_state_d = NP_1;
        end
      end

      NP_1: begin
        adc_chn_sel_o = 2'b10;
        if (adc_d_val_i) begin//sample chn1 value
          fsm_state_d = NP_EVAL;
        end
      end

      NP_EVAL: begin
        // do not transition forward until handshake with ADC is complete
        if (!adc_d_val_i) begin
          ld_match = 1'b1;
          // if there is no match, clear counter and begin sampling again.
          // if there is a match, there are 3 conditions:
          // 1. the sample count is less than the threshold -> still attempting to make a new match,
          //    keep sampling.
          // 2. the sample count is equal to the threshold -> a new match has just been made, go to
          //    DONE.
          // 3, the sample count is greater than the threshold -> this is a continued stable match,
          //    keep sampling.
          if (!stay_match) begin
            fsm_state_d = NP_0;
            np_sample_cnt_clr = 1'b1;
          end else if (np_sample_cnt_q < np_sample_cnt_thresh) begin
            fsm_state_d = NP_0;
            np_sample_cnt_en = 1'b1;
          end else if (np_sample_cnt_q == np_sample_cnt_thresh) begin
            fsm_state_d = NP_DONE;
            np_sample_cnt_en = 1'b1;
          end else if (np_sample_cnt_q > np_sample_cnt_thresh) begin
            fsm_state_d = NP_0;
          end
        end
      end

      // delay done assertion by one cycle to match with channel register timing
      NP_DONE: begin
        adc_ctrl_done_o = 1'b1;
        fsm_state_d = NP_0;
      end

      default: fsm_state_d = PWRDN;
    endcase
  end

   `ASSUME(LpSampleCntCfg_M, cfg_lp_sample_cnt_i > '0, clk_aon_i, !rst_aon_ni)
   `ASSUME(NpSampleCntCfg_M, cfg_np_sample_cnt_i > '0, clk_aon_i, !rst_aon_ni)
   `ASSERT(NpCntClrPwrDn_A, fsm_state_q == PWRDN |-> (np_sample_cnt_q == '0),
           clk_aon_i, !rst_aon_ni)

   // This statement should hold true even during low power scanning
   `ASSERT(NpCntClrMisMatch_A, ld_match & !stay_match |=>
           (np_sample_cnt_q == '0), clk_aon_i, !rst_aon_ni)

endmodule
