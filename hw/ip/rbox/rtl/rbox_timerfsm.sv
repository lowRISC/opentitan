// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description RBOX timer-based FSM module

module rbox_timerfsm #(
  parameter int unsigned TIMERBIT = 16
  ) (
  input                clk_aon_i,
  input                rst_slow_ni,
  input                trigger_i,
  input [TIMERBIT-1:0] cfg_timer_i,
  input                cfg_l2h_en_i,
  input                cfg_h2l_en_i,
  output logic         timer_l2h_cond_met,
  output logic         timer_h2l_cond_met

);

  logic trigger_q;
  logic trigger_h2l, trigger_l2h, trigger_h2h, trigger_l2l;
  logic trigger_tgl, trigger_sty;

  logic [TIMERBIT-1:0] timer_cnt_d, timer_cnt_q;
  logic timer_cnt_clr, timer_cnt_en;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_trigger_reg
    if (!rst_slow_ni) begin
      trigger_q    <= 1'b0;
    end else begin
      trigger_q    <= trigger_i;
    end
  end

  assign trigger_h2l = (trigger_q == 1'b1) && (trigger_i == 1'b0);
  assign trigger_l2h = (trigger_q == 1'b0) && (trigger_i == 1'b1);
  assign trigger_h2h = (trigger_q == 1'b1) && (trigger_i == 1'b1);
  assign trigger_l2l = (trigger_q == 1'b0) && (trigger_i == 1'b0);
  assign trigger_tgl = trigger_q != trigger_i;
  assign trigger_sty = trigger_q == trigger_i;

  //three-state FSM
  //IDLE->WAITL2H->DONEL2H or IDLE->WAITH2L->DONEH2L
  //The input signals can be inverted. Hence, both paths
  //FSM will detect a L2H or H2L transition to enter the wait state
  //debounce timer defines the time to wait for input to stablize
  //FSM will check the input after the debounce period
  typedef enum logic [2:0] {
                            IDLE = 3'h0,
                            WAITL2H = 3'h1,
                            WAITH2L = 3'h2,
                            DONEL2H = 3'h3,
                            DONEH2L = 3'h4
                            } timer_state_e;

  timer_state_e timer_state_q, timer_state_d;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_timer_state_reg
    if (!rst_slow_ni) begin
      timer_state_q    <= IDLE;
    end else begin
      timer_state_q    <= timer_state_d;
    end
  end

  assign timer_cnt_d = (timer_cnt_en) ? timer_cnt_q + 1'b1 : timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_timer_cnt_reg
    if (!rst_slow_ni) begin
      timer_cnt_q    <= '0;
    end
    else if (timer_cnt_clr) begin
      timer_cnt_q <= '0;
    end else begin
      timer_cnt_q <= timer_cnt_d;
    end
  end

  always_comb begin: timer_fsm
    timer_state_d = timer_state_q;
    //outputs
    timer_l2h_cond_met = 1'b0;
    timer_h2l_cond_met = 1'b0;
    timer_cnt_clr = 1'b0;
    timer_cnt_en = 1'b0;

    unique case (timer_state_q)
      IDLE: begin
        if (cfg_l2h_en_i &&  trigger_l2h) begin
          timer_state_d = WAITL2H;
        end
        else if (cfg_h2l_en_i &&  trigger_h2l) begin
          timer_state_d = WAITH2L;
        end
      end

      WAITL2H: begin
        if (timer_cnt_q != cfg_timer_i) begin
          timer_cnt_en = 1'b1;
        end
        else if (!trigger_h2h && (timer_cnt_q == cfg_timer_i)) begin
          timer_state_d = IDLE;
          timer_cnt_clr = 1'b1;
        end
        else if (trigger_h2h && (timer_cnt_q == cfg_timer_i)) begin
          timer_state_d = DONEL2H;
          timer_cnt_clr = 1'b1;
        end
      end

      DONEL2H: begin
        if (trigger_h2h) begin
          timer_l2h_cond_met = 1'b1;
        end
        else if (trigger_h2l) begin
          timer_state_d = IDLE;
        end
      end

      WAITH2L: begin
        if (timer_cnt_q != cfg_timer_i) begin
          timer_cnt_en = 1'b1;
        end
        else if (!trigger_l2l && (timer_cnt_q == cfg_timer_i)) begin
          timer_state_d = IDLE;
          timer_cnt_clr = 1'b1;
        end
        else if (trigger_l2l && (timer_cnt_q == cfg_timer_i)) begin
          timer_state_d = DONEH2L;
          timer_cnt_clr = 1'b1;
        end
      end

      DONEH2L: begin
        if (trigger_l2l) begin
          timer_h2l_cond_met = 1'b1;
        end
        else if (trigger_l2h) begin
          timer_state_d = IDLE;
        end
      end
      default: timer_state_d = IDLE;
    endcase
  end

endmodule
