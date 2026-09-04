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
  output reset_trx_o,

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
  logic enabled_q, enabling;
  assign enabling  = enable_i & ~enabled_q;
  assign resetting = |{enabling, sw_reset_i, te_recov_i};

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      // Ensure that the Target transceiver logic is reset whenever the IP block is reset.
      reset_trx_q <= 1'b1;
      enabled_q   <= 1'b0;
    end else begin
      reset_trx_q <= resetting;
      enabled_q   <= enable_i;
    end
  end

  // For an individual reset-generating event, this should be a single-cycle pulse; more generally,
  // the timer (`i3c_timers`) will put the transceiver into reset upon assertion of this output, and
  // start measuring from its deassertion.
  assign reset_trx_o = reset_trx_q;

  // Buffer enable state.
  logic buf_en_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) buf_en_q <= 1'b0;  // Input buffers are disabled when the IP block is reset.
    else if (resetting) buf_en_q <= 1'b0;
    else if (bus_avail_i) buf_en_q <= enabled_q;
  end
  assign inbuf_en_o = buf_en_q;

endmodule
