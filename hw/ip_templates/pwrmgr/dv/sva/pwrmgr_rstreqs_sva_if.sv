// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has some assertions that check the pwrmgr rstreqs and reset_cause output is set per the
// reset requests the pwrmgr receives or generates.
interface pwrmgr_rstreqs_sva_if
  import pwrmgr_pkg::*, pwrmgr_reg_pkg::*;
(
  input logic                    clk_i,
  input logic                    rst_ni,
  input logic                    clk_slow_i,
  input logic                    rst_slow_ni,

   // Input causes resets.
  input logic [ NumRstReqs-1:0]  rstreqs_i,
  input logic [ NumRstReqs-1:0]  reset_en,
  input logic                    sw_rst_req_i,
  input logic                    main_rst_req_i,
  input logic                    esc_rst_req_i,
  input logic                    ndm_rst_req_i,
  // outputs
  input logic                    main_pd_n,
  input reset_cause_e            reset_cause,
  input logic [HwResetWidth-1:0] rstreqs
);

  // output reset cycle with a clk enable disable
  localparam int MIN_MAIN_RST_CYCLES = 0;
  localparam int MAX_MAIN_RST_CYCLES = 400;
  `define MAIN_RST_CYCLES ##[MIN_MAIN_RST_CYCLES:MAX_MAIN_RST_CYCLES]

  // The timing of the escalation reset is determined by the slow clock, but will not propagate if
  // the non-slow clock is off. We use the regular clock and multiply the clock cycles times the
  // clock ratio.
  localparam int FAST_TO_SLOW_FREQ_RATIO = 120;

  localparam int MIN_ESC_RST_CYCLES = 0;
  localparam int MAX_ESC_RST_CYCLES = 4 * FAST_TO_SLOW_FREQ_RATIO;
  `define ESC_RST_CYCLES ##[MIN_ESC_RST_CYCLES:MAX_ESC_RST_CYCLES]

  bit disable_sva;
  bit reset_or_disable;

  always_comb reset_or_disable = !rst_ni || !rst_slow_ni || disable_sva;

  // Reset ins to outs.
  for (genvar rst = 0; rst < NumRstReqs; ++rst) begin : gen_hw_resets
    `ASSERT(HwResetOn_A,
            $rose(
                rstreqs_i[rst] && reset_en[rst]
            ) |-> `MAIN_RST_CYCLES rstreqs[rst] && reset_cause == HwReq, clk_slow_i,
            reset_or_disable)
    `ASSERT(HwResetOff_A,
            $fell(
                rstreqs_i[rst] && reset_en[rst]
            ) |-> `MAIN_RST_CYCLES !rstreqs[rst] && reset_cause != HwReq, clk_slow_i,
            reset_or_disable)
  end

  // This is used to ignore main_rst_req_i (wired to rst_main_n) if it happens during low power,
  // since as part of deep sleep rst_main_n will trigger and not because of a power glitch.
  logic rst_main_n_ignored_for_main_pwr_rst;
  always_ff @(posedge clk_slow_i or negedge rst_slow_ni) begin
    if (!rst_slow_ni) begin
      rst_main_n_ignored_for_main_pwr_rst <= 0;
    end else if (!main_pd_n && reset_cause == LowPwrEntry) begin
      rst_main_n_ignored_for_main_pwr_rst <= 1;
    end else if (reset_cause != LowPwrEntry) begin
      rst_main_n_ignored_for_main_pwr_rst <= 0;
    end
  end

  `ASSERT(MainPwrRstOn_A,
          $rose(
              main_rst_req_i && !rst_main_n_ignored_for_main_pwr_rst
          ) |-> `MAIN_RST_CYCLES rstreqs[ResetMainPwrIdx], clk_slow_i,
          reset_or_disable)
  `ASSERT(MainPwrRstOff_A,
          $fell(
              main_rst_req_i
          ) |-> `MAIN_RST_CYCLES !rstreqs[ResetMainPwrIdx], clk_slow_i,
          reset_or_disable)

   // Signals in EscRstOn_A and EscRstOff_A are sampled with slow and fast clock.
   // Since fast clock can be gated, use fast clock to evaluate cycle delay
   // to avoid spurious failure.
  `ASSERT(EscRstOn_A,
          $rose(
              esc_rst_req_i
          ) |-> `ESC_RST_CYCLES rstreqs[ResetEscIdx], clk_i, reset_or_disable)
  `ASSERT(EscRstOff_A,
          $fell(
              esc_rst_req_i
          ) |-> `ESC_RST_CYCLES !rstreqs[ResetEscIdx], clk_i, reset_or_disable)

  // Software initiated resets do not affect rstreqs since rstmgr generates them.
  `ASSERT(SwResetSetCause_A,
          $rose(sw_rst_req_i) |-> MAIN_RST_CYCLES (reset_cause == HwReq), clk_i,
          reset_or_disable)

endinterface
