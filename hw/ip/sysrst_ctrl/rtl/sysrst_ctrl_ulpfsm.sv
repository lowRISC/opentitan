// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description sysrst_ctrl ULP FSM module

module sysrst_ctrl_ulpfsm #(
  parameter bit [15:0] EdgeType = "H",  // can be LH, HL and H
  parameter int unsigned TimerWidth = 16
) (
  input                         clk_i,
  input                         rst_ni,
  input                         trigger_i,
  input        [TimerWidth-1:0] cfg_timer_i,
  input                         cfg_en_i,
  output logic                  timer_cond_met_o
);

  logic trigger_q;
  logic trigger, trigger_stable;

  logic [TimerWidth-1:0] timer_cnt_d, timer_cnt_q;
  logic timer_cnt_clr, timer_cnt_en;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_trigger_reg
    if (!rst_ni) begin
      trigger_q <= 1'b0;
    end else if (!cfg_en_i) begin
      trigger_q <= 1'b0;
    end else begin
      trigger_q <= trigger_i;
    end
  end

  if (EdgeType == "LH") begin : gen_trigger_l2h
    assign trigger = (trigger_q == 1'b0) && (trigger_i == 1'b1);
    assign trigger_stable = (trigger_q == trigger_i) && (trigger_i == 1'b1);
  end else if (EdgeType == "HL") begin : gen_trigger_h2l
    assign trigger = (trigger_q == 1'b1) && (trigger_i == 1'b0);
    assign trigger_stable = (trigger_q == trigger_i) && (trigger_i == 1'b0);
  end else begin : gen_trigger_h
    assign trigger = trigger_q;
    assign trigger_stable = (trigger_q == trigger_i) && (trigger_i == 1'b1);
  end

  //three-state FSM
  //IDLE_ST->WAIT_ST->DONE_ST
  //The input signals can be inverted. Hence, both paths
  //FSM will detect a L2H or H2L transition or level H to enter the wait state
  //debounce timer defines the time to wait for input to stablize
  //FSM will check the input after the debounce period
  //FSM will stay in the DONEXXX state until SW uses cfg_fsm_rst to clear it
  typedef enum logic [1:0] {
    IDLE_ST = 2'h0,
    WAIT_ST = 2'h1,
    DONE_ST = 2'h2
  } timer_state_e;

  timer_state_e timer_state_q, timer_state_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_timer_state_reg
    if (!rst_ni) begin
      timer_state_q <= IDLE_ST;
    end else begin
      timer_state_q <= timer_state_d;
    end
  end

  assign timer_cnt_d = (timer_cnt_en) ? timer_cnt_q + 1'b1 : timer_cnt_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_timer_cnt_reg
    if (!rst_ni) begin
      timer_cnt_q <= '0;
    end else if (timer_cnt_clr) begin
      timer_cnt_q <= '0;
    end else begin
      timer_cnt_q <= timer_cnt_d;
    end
  end

  always_comb begin : p_timer_fsm
    timer_state_d = timer_state_q;
    //outputs
    timer_cond_met_o = 1'b0;
    timer_cnt_clr = 1'b0;
    timer_cnt_en = 1'b0;

    unique case (timer_state_q)
      IDLE_ST: begin
        if (cfg_en_i && trigger) begin
          timer_cnt_clr = 1'b1;
          timer_state_d = WAIT_ST;
        end
      end

      WAIT_ST: begin
        // timer has expired
        if (timer_cnt_q == cfg_timer_i) begin
          // if the trigger is stable as defined above, we are done
          if (trigger_stable) begin
            timer_state_d = DONE_ST;
            // otherwise go back to IDLE_ST
          end else begin
            timer_state_d = IDLE_ST;
          end
          // else continue counting
        end else begin
          timer_cnt_en = 1'b1;
        end
      end

      DONE_ST: timer_cond_met_o = 1'b1;

      default: timer_state_d = IDLE_ST;
    endcase
    // Force the state into IDLE_ST if FSM is disabled
    if (!cfg_en_i) begin
      timer_state_d = IDLE_ST;
    end
  end

endmodule
