// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Reset detector for I3C target; this logic detects the Target Reset pattern and is expected
// to be situated in a low power 'Always On' domain, outside of the I3C IP block itself.
//
// It does not have a free-running clock of its own, but responds directly to the
// Controller-supplied SCL signal on the I3C bus and must remain operational when the I3C IP block
// is powered down or unclocked, in order to respond to wake up signaling.
//
// The AON clock is required for the CDC to the IP register interface and the power manager.

module i3c_reset_detector
  import i3c_pkg::*;
  import prim_mubi_pkg::*;
(
  // No free-running clock from the IP block core for most of this logic; it is driven by the
  // Controller-supplied SCL and SDA. However, the output signals are presented to logic in the
  // AON domain, so we need the clock for CDC.
  input                   clk_aon_i,
  input                   rst_aon_ni,

  // Enable the input buffers and SCL/SDA propagation into the block.
  input                   enable_i,

  // Request from the IP block, AON clock domain.
  input  i3c_rstdet_req_t req_i,
  // Response to the IP block, AON clock domain.
  output i3c_rstdet_rsp_t rsp_o,

  // I3C I/O signals being monitored.
  input                   scl_i,
  input                   sda_i,

  // Control signals in response to Target Reset pattern.
  output                  wake_up_o,       // Wake from Deepest Sleep.
  output                  target_reset_o,  // I3C target only.
  output                  chip_reset_o,    // Entire chip.

  // DFT-related signals.
  input                   scan_clk_i,
  input  mubi4_t          scanmode_i
);

  // The action taken upon detection of the Target Reset pattern depends upon configuration supplied
  // earlier:
  //
  // - No Reset.
  // - Wake from Deepest Sleep.
  // - Issue Peripheral Reset.
  // - Issue Whole Target Reset.
  //
  // A second occurrence of the Target Reset pattern without an intervening acknowledgement of a
  // Peripheral Reset is escalated to a Whole Target Reset.
  //
  // Illustration of the general Target Reset Pattern, showing the 14 SDA Transitions, followed by
  // Sr (Repeated Start) and P (stoP).
  //    ______   _   _   _   _   _   _   ____    ___
  // SDA      \_/ \_/ \_/ \_/ \_/ \_/ \_/    \__/
  //     __                                _________
  // SCL   \______________________________/  Sr P
  //
  // See Figures 67 and 68 for more detail.

  logic scanmode;
  assign scanmode = mubi4_test_true_strict(scanmode_i);

  // Responses to detection of the Target Reset Pattern.
  logic wake_up_q;
  logic target_reset_q;
  logic chip_reset_q;

  // Request synchronized to SDA clock domain.
  i3c_rstdet_req_t req_sync;
  // Response synchronized to AON clock domain.
  i3c_rstdet_rsp_t rsp_sync;
  assign rsp_o = rsp_sync;

  // SCL and SDA inputs, and their negations, are all required within this detector.
  // Additionally the 'enable_i' signal can be used to protect the logic from disconnected SCL/SDA
  // inputs or other activity when the Target logic is not ready to process traffic.
  logic scl_buf;
  logic scl_buf_n;
  logic sda_clk;
  logic sda_clk_n;

  i3c_input_buffers #(.NumSDALanes(1)) u_targ_inbufs (
    .enable_i   (enable_i),

    // I3C target inputs.
    .scl_i      (scl_i),
    .sda_i      (sda_i),

    // Clock signals.
    .scl_buf_o  (scl_buf),
    .scl_buf_no (scl_buf_n),
    .sda0_clk_o (sda_clk),
    .sda0_clk_no(sda_clk_n),
    .sda_buf_o  (),  // Not used.

    // DFT-related signals.
    .scan_clk_i (scan_clk_i),
    .scanmode_i (scanmode)
  );

  // TODO(#31335): scan mode will need to be able to issue a reset and scan these flops too.

  // Capture configuration using the first two positive edges of SDA.
  // - there are 7 or 8 positive edges within the target reset pattern itself, so we readily
  //   capture the latest configuration even if receiving a reset pattern.
  prim_flop_2sync #(.Width($bits(i3c_rstdet_req_t))) u_cfg_sync (
    .clk_i  (sda_clk),
    .rst_ni (rst_aon_ni),
    .d_i    (req_i),
    .q_o    (req_sync)
  );

  // The later stages of the Target Reset detector may be clock-gated, once the configuration from
  // the IP clock domain is known.
  logic active;
  assign active = req_sync.activate;

  // Target Reset detection; operational in all modes (I3C Basic 4.3.9.3).
  // - count 7 or 8 positive edges of SDA before SCL rises, followed by Sr and P.
  logic [2:0] rst_cnt;
  always_ff @(posedge sda_clk or negedge rst_aon_ni) begin
    if (!rst_aon_ni) rst_cnt <= 'b0;
    else if (scl_buf) rst_cnt <= 'b0;  // stoP resets the counter.
    else rst_cnt <= rst_cnt + ~&rst_cnt;
  end

  // Detection is cleared by firmware deasserting the `activate` request signal.
  // - this needs to be done asynchronously because we cannot rely upon SCL/SDA activity.
  wire reset_ni = rst_aon_ni & req_i.activate;

  // Reset the Sr and P detection once they have fired, and wait anew for the requisite number of
  // SDA transitions.
  logic reset_detected;
  wire reset_srp_ni = reset_ni & !reset_detected;

  // Following 14 transitions on SDA, a rising SCL edge primes the detection of an ensuing Sr and P.
  logic poss_reset_pend;
  always_ff @(posedge scl_buf or negedge reset_srp_ni) begin
    if (!reset_srp_ni) poss_reset_pend <= 1'b0;
    else poss_reset_pend <= (rst_cnt >= 'h7);
  end
  // Detection of Sr (restart).
  logic poss_reset_start;
  always_ff @(posedge sda_clk_n or negedge reset_srp_ni) begin
    if (!reset_srp_ni) poss_reset_start <= 1'b0;
    else poss_reset_start <= scl_buf & poss_reset_pend;
  end

  // Detection of P (stop) resets the internal logic, to be ready for a subsequent pattern.
  always_ff @(posedge sda_clk or negedge rst_aon_ni) begin
    if (!rst_aon_ni) reset_detected <= 1'b0;
    else reset_detected <= poss_reset_start & !reset_detected;
  end

  // Detection of P (stop) actions the reset.
  always_ff @(posedge sda_clk or negedge reset_ni) begin
    if (!reset_ni) begin
      wake_up_q       <= 1'b0;
      target_reset_q  <= 1'b0;
      chip_reset_q    <= 1'b0;
    end else if (active & scl_buf & poss_reset_start) begin
      wake_up_q       <= req_sync.deep_sleep;
      target_reset_q  <= req_sync.rst_periph;
      // Reset escalation; upon receipt of a second Target Reset signal without a
      // 'Peripheral Reset' being acknowledged, we are recommended to issue a reset of the
      // 'Whole Target' (I3C Basic 4.3.9.4).
      chip_reset_q    <= req_sync.rst_target | target_reset_q;
    end
  end

  i3c_rstdet_rsp_t rsp_int;
  assign rsp_int.active       = req_sync.activate;
  assign rsp_int.wake_up_det  = wake_up_q;
  assign rsp_int.peri_rst_det = target_reset_q;
  assign rsp_int.targ_rst_det = chip_reset_q;

  // The activation signals are captured onto the AON clock domain, to resolve CDC issues with
  // both the register interface of the IP block and the recipient of the notification signals
  // (usually some form of power manager).
  //
  // Note: with a typical AON clock frequency of 200kHz, the verdict will not be available for
  // 5us-15us, but the Target is not required to respond quickly to a Target Reset pattern.
  prim_flop_2sync #(.Width($bits(i3c_rstdet_rsp_t))) u_out_sync (
    .clk_i (clk_aon_i),
    .rst_ni(rst_aon_ni),
    .d_i   (rsp_int),
    .q_o   (rsp_sync)
  );

  // These are active high signals which will be asserted for an indefinite period.
  //
  // Wake from Deepest sleep.
  assign wake_up_o      = rsp_sync.wake_up_det;
  // I3C Peripheral only.
  assign target_reset_o = rsp_sync.peri_rst_det;
  // Entire chip.
  assign chip_reset_o   = rsp_sync.targ_rst_det;

endmodule
