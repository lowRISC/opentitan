// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl ULP FSM module

module sysrst_ctrl_ulpfsm #(
  parameter EDGE_TYPE = "H", // can be LH, HL and H
  parameter int unsigned TIMERBIT = 16
  ) (
  input                clk_aon_i,
  input                rst_aon_ni,
  input                trigger_i,
  input [TIMERBIT-1:0] cfg_timer_i,
  input                cfg_en_i,
  output logic         timer_cond_met_o

);

  logic trigger_q;
  logic trigger, trigger_stable;

  logic [TIMERBIT-1:0] timer_cnt_d, timer_cnt_q;
  logic timer_cnt_clr, timer_cnt_en;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_trigger_reg
    if (!rst_aon_ni) begin
      trigger_q    <= 1'b0;
    end
    else if (!cfg_en_i) begin
      trigger_q <= 1'b0;
    end else begin
      trigger_q    <= trigger_i;
    end
  end

  if (EDGE_TYPE == "LH") begin : gen_trigger_l2h
    assign trigger = (trigger_q == 1'b0) && (trigger_i == 1'b1);
    assign trigger_stable = (trigger_q == trigger_i) && (trigger_i == 1'b1);
  end else if (EDGE_TYPE == "HL")  begin : gen_trigger_h2l
    assign trigger = (trigger_q == 1'b1) && (trigger_i == 1'b0);
    assign trigger_stable = (trigger_q == trigger_i) && (trigger_i == 1'b0);
  end else begin: gen_trigger_h
    assign trigger = trigger_q;
    assign trigger_stable = (trigger_q == trigger_i) && (trigger_i == 1'b1);
  end

  //three-state FSM
  //IDLE->WAIT->DONE
  //The input signals can be inverted. Hence, both paths
  //FSM will detect a L2H or H2L transition or level H to enter the wait state
  //debounce timer defines the time to wait for input to stablize
  //FSM will check the input after the debounce period
  //FSM will stay in the DONEXXX state until SW uses cfg_fsm_rst to clear it
  typedef enum logic [1:0] {
                            IDLE = 2'h0,
                            WAIT = 2'h1,
                            DONE = 2'h2
                            } timer_state_e;

  timer_state_e timer_state_q, timer_state_d;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_timer_state_reg
    if (!rst_aon_ni) begin
      timer_state_q    <= IDLE;
    end
    else begin
      timer_state_q    <= timer_state_d;
    end
  end

  assign timer_cnt_d = (timer_cnt_en) ? timer_cnt_q + 1'b1 : timer_cnt_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin: i_timer_cnt_reg
    if (!rst_aon_ni) begin
      timer_cnt_q    <= '0;
    end
    else if (timer_cnt_clr ) begin
      timer_cnt_q <= '0;
    end else begin
      timer_cnt_q <= timer_cnt_d;
    end
  end

  always_comb begin: timer_fsm
    timer_state_d = timer_state_q;
    //outputs
    timer_cond_met_o = 1'b0;
    timer_cnt_clr = 1'b0;
    timer_cnt_en = 1'b0;

    unique case (timer_state_q)
      IDLE: begin
        if (cfg_en_i &&  trigger) begin
          timer_cnt_clr = 1'b1;
          timer_state_d = WAIT;
        end
      end

      WAIT: begin
        // timer has expired
        if (timer_cnt_q == cfg_timer_i) begin
          // if the trigger is stable as defined above, we are done
          if (trigger_stable) begin
            timer_state_d = DONE;
          // otherwise go back to idle
          end else begin
            timer_state_d = IDLE;
          end
        // else continue counting
        end else begin
          timer_cnt_en = 1'b1;
        end
      end

      DONE: timer_cond_met_o = 1'b1;

      default: timer_state_d = IDLE;
    endcase
    // Force the state into IDLE if FSM is disabled
    if (!cfg_en_i) begin
      timer_state_d = IDLE;
    end
  end

endmodule
