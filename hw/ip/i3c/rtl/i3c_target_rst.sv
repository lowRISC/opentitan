// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Generation of asynchronous reset for the Target-side transceiver logic.
module i3c_target_rst (
  // Main IP clock and reset.
  input  clk_i,
  input  rst_ni,

  // Control.
  input  enable_i,
  input  sw_reset_i,
  input  te_recov_i,

  // Bus monitoring.
  input  bus_avail_i,

  // Initiate asynchronous reset of transceiver logic.
  // - the active low reset signal is asserted under the control of a programmable timer,
  //   typically for 5 microseconds.
  output reset_trig_o,

  // Buffer enable for SCL and SDA.
  output inbuf_en_o
);

  // The Target-side transceiver logic is driven by the SCL signal from the Active Controller on the
  // I3C bus, which means that any reset driven into the block must be considered asynchronous and
  // could collide with SCL/SDA bus activity.
  //
  // To address this and produce a clean reset, we disable the SCL and SDA buffers into the
  // logic, produce a timed, prolonged asynchronous reset and then monitor the SCL/SDA activity
  // using the main IP clock until such time as the Bus Available condition has occurred.
  //
  // This applies to the 'disabled->enabled' transition of the Target logic, software-initiated
  // reset requests, and hardware-initiated error recovery when required.

  logic reset_trx_q, resetting;

  // TODO(#31337): This logic is temporary and it is anticipated that the global state of the
  // Target logic will be controlled by a simple FSM within `i3c_target`, in a manner similar to
  // that employed by the Controller.
  assign resetting = |{~enable_i,                // Hold the transceiver in reset when disabled.
                       sw_reset_i, te_recov_i};  // Single-cycle pulse events.

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Ensure that the Target transceiver logic is reset whenever the IP block is reset.
      reset_trx_q <= 1'b1;
    end else reset_trx_q <= resetting;
  end

  // For an individual reset-generating event, this should be a single-cycle pulse; more generally,
  // the timer (`i3c_timers`) will put the transceiver into reset upon assertion of this output, and
  // start measuring from its deassertion.
  assign reset_trig_o = reset_trx_q;

  // Buffer enable state.
  // - enable/disable the input buffers only when the Bus Available condition holds.
  // - when disabling the input buffers in response to a reset (software-intitiated, error etc)
  //   we hold the input buffers enabled until the reset is asserted; this just reduces the chance
  //   of glitching the I3C bus, but the reset should really only be used when the transceiver
  //   is already disabled and disconnected.
  localparam int unsigned BufDisableDelCycles = 4;  // Includes a couple of extra IP clock cycles.

  logic [BufDisableDelCycles-1:0] reset_del_q;
  logic buf_en_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reset_del_q <= '0;
      buf_en_q    <= 1'b0;  // Input buffers are disabled when the IP block is reset.
    end else if (reset_del_q[0]) begin
      reset_del_q <= '0;
      buf_en_q    <= 1'b0;
    end else begin
      // Delay the disconnection of the input when there is active traffic. When the input buffers
      // are disabled, the transceiver logic will see an Idle bus (SCL and SDA both high), but we
      // want to avoid that causing spurious behavior in the transceiver if it _is_ transmitting.
      reset_del_q <= {reset_trx_q, reset_del_q[BufDisableDelCycles-1:1]};

      // Change the input buffer enable only during the Bus Available condition - at least 1us
      // elapsed since I3C activity was last observed) - to prevent corrupted traffic entering the
      // transceiver logic.
      if (bus_avail_i) buf_en_q <= enable_i;
    end
  end
  assign inbuf_en_o = buf_en_q;

endmodule
