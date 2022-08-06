// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Debounce and detector module.
//
// The module is able to detect either low/high levels, or transitions to low/high levels (edges).
// The event type to trigger on can be configured via the EventType parameter.
//
// Whenever a trigger event is seen at the input (for instance a transition to low) the module first
// backs off for the amount of debounce cycles configured through cfg_debounce_timer_i. Then the
// module samples the input value again and if it still matches the active level (low in this
// example), the module goes into detection mode. In detection mode, the module checks whether the
// trigger signal remains stable for the number of cycles configured via cfg_detect_timer_i. If it
// does, event_detected_pulse_o will be pulsed high for one cycle and event_detected_o will be held
// high until the input trigger value changes.
//
// Note that if the module is configured as "Sticky", the module needs to be explicitly disabled
// and enabled again in order to reset the internal FSM into its idle state.
//

module sysrst_ctrl_detect
  import sysrst_ctrl_pkg::*;
#(
  // The module only contains one counter to implement both timers.
  // The width of that counter is set to the maximum of the two values below.
  parameter int unsigned DebounceTimerWidth = 16,
  parameter int unsigned DetectTimerWidth = 32,
  // Determines the event type that the detector should be sensitive to.
  parameter event_t      EventType = LowLevel,
  // If this parameter is set to 1, the l2h_detected_o and h2l_detected_o conditions can only be
  // reset by disabling the corresponding detector (cfg_l2h_en_i or cfg_h2l_en_i).
  parameter bit          Sticky = 0
) (
  input                                 clk_i,
  input                                 rst_ni,
  // Trigger input signal.
  input                                 trigger_i,
  // Debounce and detection timer thresholds.
  input        [DebounceTimerWidth-1:0] cfg_debounce_timer_i,
  input        [DetectTimerWidth-1:0]   cfg_detect_timer_i,
  // Enables the detector module.
  // Note that the internal state machine can be reset to its idle state by disabling the module.
  input                                 cfg_enable_i,
  // Held high after detection of the event as long as the trigger level is correct.
  output logic                          event_detected_o,
  // Pulsed high for one cycle when the event is detected.
  output logic                          event_detected_pulse_o
);

  //////////////////
  // Detect Event //
  //////////////////

  // This just decodes the active level needed for detection.
  logic trigger_active;
  if (EventType inside {LowLevel, EdgeToLow}) begin : gen_trigger_active_low
    assign trigger_active = (trigger_i == 1'b0);
  end else begin : gen_trigger_active_high
    assign trigger_active = (trigger_i == 1'b1);
  end

  // In case of edge events, we also need to detect the transition.
  logic trigger_event;
  if (EventType inside {EdgeToLow, EdgeToHigh}) begin : gen_trigger_event_edge
    // This flop is always active, no matter the enable state.
    logic trigger_active_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin : p_trigger_reg
      if (!rst_ni) begin
        trigger_active_q <= 1'b0;
      end else begin
        trigger_active_q <= trigger_active;
      end
    end

    assign trigger_event = trigger_active & ~trigger_active_q;
  // In case of level events, the event is equal to the level being active.
  end else begin : gen_trigger_event_level
    assign trigger_event = trigger_active;
  end

  /////////////////
  // Timer Logic //
  /////////////////

  // Take the maximum width of both timer values.
  localparam int unsigned TimerWidth =
      (DetectTimerWidth > DebounceTimerWidth) ? DetectTimerWidth : DebounceTimerWidth;

  logic cnt_en, cnt_clr;
  logic [TimerWidth-1:0] cnt_d, cnt_q;
  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 :
                             cnt_q;


  logic cnt_done, thresh_sel;
  logic [TimerWidth-1:0] thresh;
  assign thresh = (thresh_sel) ? TimerWidth'(cfg_detect_timer_i) :
                                 TimerWidth'(cfg_debounce_timer_i);
  assign cnt_done = (cnt_q >= thresh);

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_cnt_reg
    if (!rst_ni) begin
      cnt_q <= '0;
    end else begin
      cnt_q <= cnt_d;
    end
  end

  /////////
  // FSM //
  /////////

  typedef enum logic [1:0] {
    IdleSt,
    DebounceSt,
    DetectSt,
    StableSt
  } state_t;

  state_t state_d, state_q;

  always_comb begin : p_fsm
    state_d = state_q;

    // Counter controls (clear has priority).
    cnt_clr = 1'b0;
    cnt_en = 1'b0;

    // Detected outputs
    event_detected_o = 1'b0;
    event_detected_pulse_o = 1'b0;

    // Threshold select
    // 0: debounce
    // 1: detect
    thresh_sel = 1'b0;

    unique case (state_q)
      ////////////////////////////////////////////
      // We are waiting for the event to occur.
      // This can be either a specific level or edge,
      // depending on the configuration.
      IdleSt: begin
        // Stay here if the detector is disabled.
        if (trigger_event && cfg_enable_i) begin
          state_d = DebounceSt;
          cnt_en = 1'b1;
        end
      end
      ////////////////////////////////////////////
      // If an event has occurred, we back off for
      // the amount of debounce cycles configured.
      // Once the timer has expired, we sample the
      // signal again and check whether it has the
      // correct level. If so, we move on to the
      // detection stage, otherwise we fall back.
      DebounceSt: begin
        cnt_en = 1'b1;
        // Unconditionally go back to idle if the detector is disabled.
        if (!cfg_enable_i) begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
        end else if (cnt_done) begin
          cnt_clr = 1'b1;
          if (trigger_active) begin
            state_d = DetectSt;
          end else begin
            state_d = IdleSt;
          end
        end
      end
      ////////////////////////////////////////////
      // Once the debounce period has passed, we
      // check whether the signal remains stable
      // throughout the entire detection period.
      // If it is not stable at any cycle, we fall
      // back to idle.
      DetectSt: begin
        thresh_sel = 1'b1;
        cnt_en = 1'b1;
        // Go back to idle if either the trigger level is not active anymore, or if the
        // detector is disabled.
        if (!cfg_enable_i || !trigger_active) begin
          state_d = IdleSt;
          cnt_clr = 1'b1;
        // If the trigger is active, count up.
        end else begin
          if (cnt_done) begin
            state_d = StableSt;
            cnt_clr = 1'b1;
            event_detected_o = 1'b1;
            event_detected_pulse_o = 1'b1;
          end
        end
      end
      ////////////////////////////////////////////
      // At this point we have detected the event
      // and monitor whether the signal remains stable.
      StableSt: begin
        // Go back to idle if either the trigger level is not active anymore, or if the detector is
        // disabled. Note that if the detector is sticky, it has to be explicitly disabled in order
        // to go back to the idle state.
        if (!cfg_enable_i || (!trigger_active && !Sticky)) begin
          state_d = IdleSt;
        // Otherwise keep the event detected output signal high.
        end else begin
          event_detected_o = 1'b1;
        end
      end
      ////////////////////////////////////////////
      // This is a full case statement
      default: ;
    endcase // state_q
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_fsm_reg
    if (!rst_ni) begin
      state_q <= IdleSt;
    end else begin
      state_q <= state_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(DisabledIdleSt_A, !cfg_enable_i |=> state_q == IdleSt)
  `ASSERT(DisabledNoDetection_A, !cfg_enable_i |-> !event_detected_o && !event_detected_pulse_o)

  if (EventType inside {LowLevel, EdgeToLow}) begin : gen_low_level_sva
    `ASSERT(LowLevelEvent_A, !trigger_i === trigger_active)
  end else begin: gen_high_level_sva
    `ASSERT(HighLevelEvent_A, trigger_i === trigger_active)
  end

  if (EventType == LowLevel) begin : gen_low_event_sva
    `ASSERT(LowLevelEvent_A, !trigger_i === trigger_event)
  end else if (EventType == HighLevel) begin : gen_high_event_sva
    `ASSERT(HighLevelEvent_A, trigger_i === trigger_event)
  end else if (EventType == EdgeToLow) begin : gen_edge_to_low_event_sva
    `ASSERT(EdgeToLowEvent_A, !trigger_i && $past(trigger_i) |-> trigger_event)
  end else if (EventType == EdgeToLow) begin : gen_edge_to_high_event_sva
    `ASSERT(EdgeToHighEvent_A, trigger_i && !$past(trigger_i) |-> trigger_event)
  end

  `ASSERT(EnterDebounceSt_A,
      state_q == IdleSt && cfg_enable_i && trigger_event
      |=>
      state_q == DebounceSt)

  `ASSERT(EnterDetectSt_A,
      state_q == DebounceSt && cnt_q >= cfg_debounce_timer_i && trigger_active && cfg_enable_i
      |=>
      state_q == DetectSt)

  `ASSERT(DetectStDropOut_A,
      state_q == DetectSt && !trigger_active && cfg_enable_i
      |=>
      state_q == IdleSt)

  `ASSERT(EnterStableSt_A,
      state_q == DetectSt && cnt_q >= cfg_detect_timer_i && trigger_active && cfg_enable_i
      |=>
      state_q == StableSt)

  `ASSERT(StayInStableSt,
      state_q == StableSt && trigger_active && cfg_enable_i
      |=>
      state_q == StableSt)

  if (Sticky) begin : gen_sticky_sva
    `ASSERT(StableStDropOut_A,
        state_q == StableSt && cfg_enable_i && !trigger_active
        |=>
        state_q == StableSt)
  end else begin : gen_not_sticky_sva
    `ASSERT(StableStDropOut_A,
        state_q == StableSt && cfg_enable_i && !trigger_active
        |=>
        state_q == IdleSt)
  end

  `ASSERT(DetectedOut_A,
      state_q == StableSt && trigger_active && cfg_enable_i ||
      state_q == DetectSt && cnt_q >= cfg_detect_timer_i && trigger_active && cfg_enable_i
      |->
      event_detected_o)

  `ASSERT(DetectedPulseOut_A,
      state_q == DetectSt && cnt_q >= cfg_detect_timer_i && trigger_active && cfg_enable_i
      |->
      event_detected_pulse_o)

  `ASSERT(PulseIsPulse_A,
      event_detected_pulse_o |=> !event_detected_pulse_o)

  // Counter does not wrap around unless it is explicitly cleared
  `ASSERT(CntNoWrap_A,
      !cnt_clr
      |=>
      cnt_q >= $past(cnt_q))

  `ASSERT(CntClr_A,
      cnt_clr
      |=>
      cnt_q == '0)

  `ASSERT(CntIncr_A,
      cnt_en && !cnt_clr
      |=>
      cnt_q == $past(cnt_q) + 1)

endmodule : sysrst_ctrl_detect
