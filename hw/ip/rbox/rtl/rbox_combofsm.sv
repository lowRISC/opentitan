// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description RBOX combo detection FSM module

module rbox_combofsm #(
  parameter int unsigned TIMER1BIT = 16,
  parameter int unsigned TIMER2BIT = 32
  ) (
  input                clk_aon_i,
  input                rst_slow_ni,
  input                trigger_h_i,//input vector is all "1"
  input                trigger_l_i,//input vector is all "0"
  input [TIMER1BIT-1:0] cfg_timer1_i,//debounce
  input [TIMER2BIT-1:0] cfg_timer2_i,//detection
  input                cfg_h2l_en_i,
  output logic         timer_h2l_cond_met

);

  logic trigger_h_q, trigger_l_q;
  logic trigger_h2l, trigger_l2h, trigger_h2h, trigger_l2l;

  logic [TIMER1BIT-1:0] timer1_cnt_d, timer1_cnt_q;
  logic timer1_cnt_clr, timer1_cnt_en;
  logic [TIMER2BIT-1:0] timer2_cnt_d, timer2_cnt_q;
  logic timer2_cnt_clr, timer2_cnt_en;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_trigger_h_reg
    if (!rst_slow_ni) begin
      trigger_h_q    <= 1'b0;
    end else begin
      trigger_h_q    <= trigger_h_i;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_trigger_l_reg
    if (!rst_slow_ni) begin
      trigger_l_q    <= 1'b0;
    end else begin
      trigger_l_q    <= trigger_l_i;
    end
  end

  assign trigger_h2l = (trigger_h_q == 1'b1) && (trigger_l_i == 1'b1);
  assign trigger_l2h = (trigger_l_q == 1'b1) && (trigger_h_i == 1'b1);
  assign trigger_h2h = (trigger_h_q == 1'b1) && (trigger_h_i == 1'b1);
  assign trigger_l2l = (trigger_l_q == 1'b1) && (trigger_l_i == 1'b1);

  //Four-state FSM
  //IDLE->WAIT1->WAIT2->DONE
  //FSM will detect a H2L transition to enter the wait1 state
  //debounce timer defines the time for input to stablize
  //FSM will check the input after the debounce period
  //If the input stays at low, enter the wait2 state
  //Detection timer defines the time for input to be held(pressed)
  //FSM will enter the done state after the detection period
  typedef enum logic [1:0] {
                            IDLE = 2'h0,
                            WAIT1 = 2'h1,
                            WAIT2 = 2'h2,
                            DONE = 2'h3
                            } timer_state_e;

  timer_state_e timer_state_q, timer_state_d;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_timer_state_reg
    if (!rst_slow_ni) begin
      timer_state_q    <= IDLE;
    end else begin
      timer_state_q    <= timer_state_d;
    end
  end

  assign timer1_cnt_d = (timer1_cnt_en) ? timer1_cnt_q + 1'b1 : timer1_cnt_q;
  assign timer2_cnt_d = (timer2_cnt_en) ? timer2_cnt_q + 1'b1 : timer2_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_timer1_cnt_reg
    if (!rst_slow_ni) begin
      timer1_cnt_q    <= '0;
    end
    else if (timer1_cnt_clr) begin
      timer1_cnt_q <= '0;
    end else begin
      timer1_cnt_q <= timer1_cnt_d;
    end
  end

  always_ff @(posedge clk_aon_i or negedge rst_slow_ni) begin: i_timer2_cnt_reg
    if (!rst_slow_ni) begin
      timer2_cnt_q    <= '0;
    end
    else if (timer2_cnt_clr) begin
      timer2_cnt_q <= '0;
    end else begin
      timer2_cnt_q <= timer2_cnt_d;
    end
  end

  always_comb begin: timer_fsm
    timer_state_d = timer_state_q;
    //outputs
    timer_h2l_cond_met = 1'b0;
    timer1_cnt_clr = 1'b0;
    timer1_cnt_en = 1'b0;
    timer2_cnt_clr = 1'b0;
    timer2_cnt_en = 1'b0;

    unique case (timer_state_q)
      IDLE: begin
        if (cfg_h2l_en_i &&  trigger_h2l) begin
          timer_state_d = WAIT1;
        end
      end

      WAIT1: begin
        if (timer1_cnt_q != cfg_timer1_i) begin
          timer1_cnt_en = 1'b1;
        end
        else if (!trigger_l2l && (timer1_cnt_q == cfg_timer1_i)) begin
          timer_state_d = IDLE;
          timer1_cnt_clr = 1'b1;
        end
        else if (trigger_l2l && (timer1_cnt_q == cfg_timer1_i)) begin
          timer_state_d = WAIT2;
          timer1_cnt_clr = 1'b1;
        end
      end

      WAIT2: begin
        if (timer2_cnt_q != cfg_timer2_i) begin
          timer2_cnt_en = 1'b1;
        end
        else if (!trigger_l2l && (timer2_cnt_q == cfg_timer2_i)) begin
          timer_state_d = IDLE;
          timer2_cnt_clr = 1'b1;
        end
        else if (trigger_l2l && (timer2_cnt_q == cfg_timer2_i)) begin
          timer_state_d = DONE;
          timer2_cnt_clr = 1'b1;
        end
      end

      DONE: begin
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
