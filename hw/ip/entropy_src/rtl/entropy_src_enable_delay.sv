// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: Logic module indicate ongoing activity of after disablement of entropy_src_core
//
// The entropy_src has a great deal of internal state, and when shutting down most of this internal
// state should be cleared.  (The two notable exceptions are the health test statistics, which are
// only cleared at the next enable, and the SHA3 conditioning sponge which accumulates unused
// entropy until a seed is generated).  There are delays as incoming RNG data is processed, and for
// ease of verification we insist all elements of the data pipeline are cleared consistently.  This
// means that once an RNG sample enters the pipeline, that sample should be reflected in the health
// tests. The SHA3 conditioner is also assumed to successfully absorb every 64-bits that enters the
// module.
//
// To acheive this consistency goal the entropy_src delays the clearing of internal data buffers
// and the state machine until:
// 1. Any unprocessed data has been counted at the health checks (regardless of the mode)
// 2. Any RNG data bound for the SHA conditioner has been received at the conditioner.
// 3. Any ongoing SHA processing operations have completed, and the main FSM has been forced
//    back to idle.
//
// This block creates a modified version of the enable pulse which:
// 1. Postpones the disable event until any flowing data has passed through the RNG, ESBIT and
//    POSTHT FIFOs.  If packpressure is encountered at the Precon FIFO, the stalled data can
//    be discarded, and so a has a maximum time limit of MaxFifoWait=3 clocks is given for this
//    check.
// 2. Once the disable signal is received, the rising edge does not occur until:
//    2a. One clock after the falling edge OR
//    2b. One clock after the SHA engine completes,
//    Whichever comes later.

module entropy_src_enable_delay import prim_mubi_pkg::*; (
  input logic  clk_i,
  input logic  rst_ni,

  input logic  enable_i,

  // Unconsumed FIFO inputs
  input logic esrng_fifo_not_empty_i,
  input logic esbit_fifo_not_empty_i,
  input logic postht_fifo_not_empty_i,

  // SHA3 conditioner inputs
  input logic   cs_aes_halt_req_i,
  input mubi4_t sha3_done_i,

  input logic bypass_mode_i,

  output logic enable_o
);

  // Maximum number of cycles to wait for FIFOs to clear out.
  // Set to 3 to allow one cycle for each FIFO in the pipeline.
  localparam int MaxFifoWait = 3;

  logic suppress_reenable;
  logic extend_enable;

  logic data_in_flight;
  logic [2:0] fifos_not_empty;

  // Flops
  logic [MaxFifoWait - 1:0] fifo_timer_d, fifo_timer_q;
  logic                     sha3_active_post_en_d, sha3_active_post_en_q;
  mubi4_t                   sha3_done_q;
  logic                     extend_enable_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sha3_active_post_en_q   <= 1'b0;
      fifo_timer_q            <= '0;
      sha3_done_q             <= prim_mubi_pkg::MuBi4False;
      extend_enable_q         <= 1'b0;
    end else begin
      sha3_active_post_en_q   <= sha3_active_post_en_d;
      fifo_timer_q            <= fifo_timer_d;
      sha3_done_q             <= sha3_done_i;
      extend_enable_q         <= extend_enable;
    end
  end

  // Output definition
  assign enable_o = (enable_i & ~suppress_reenable) | extend_enable;

  // In flight data monitoring.
  // The `fifo_timer` is a small shift register to count out the maximum number of cycles to wait
  // for the FIFOs to drain. Since this timer is very small (3 cycles), it is implemented as a shift
  // register.
  assign fifo_timer_d = enable_i ? {MaxFifoWait{1'b1}} : {fifo_timer_q[MaxFifoWait-2:0], 1'b0};
  assign fifos_not_empty = {esrng_fifo_not_empty_i, esbit_fifo_not_empty_i,
                            !bypass_mode_i & postht_fifo_not_empty_i};
  assign data_in_flight = |fifo_timer_q && |fifos_not_empty;

  // Extend the enable by at least one clock to give the FSM time to receive any last
  // Health checks.
  assign extend_enable = ((fifo_timer_q[0] | data_in_flight) & ~enable_i);

  // Pulse to extend from the falling edge of the incoming enable pulse
  // until one cycle after the SHA is done.
  assign sha3_active_post_en_d = cs_aes_halt_req_i && !enable_i ? 1'b1 :
                                 mubi4_test_true_strict(sha3_done_q) ? 1'b0 :
                                 sha3_active_post_en_q;

  // Force the output to be low until sha3_active_post_en_q falls or
  // for one more cycle after the falling each of extend_enable
  assign suppress_reenable = sha3_active_post_en_q | extend_enable_q;

endmodule
