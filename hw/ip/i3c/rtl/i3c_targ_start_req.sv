// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module generates the initial part of Target-initiated arbitrable address headers (e.g., to
// signal IBI or Controller Role Requests to the Active Controller). After the first three bits, the
// neccessary information has propagated across the CDC such that the transceiver takes over.

module i3c_targ_start_req
  import i3c_tti_pkg::*;
#(
  parameter bit Dummy = 1'b0
) (
  input                   clk_i,
  input                   rst_ni,

  // Control signals.
  input                   enable_i,
  input                   start_i,
  input                   reset_i,

  // IBI/CRR target address.
  input             [6:0] addr_i,

  // I3C bus signals, already synchronized.
  input                   scl_i,
  input                   sda_i,

  // Start request signaling to the transceiver.
  output logic            sreq_sda_od_en_o,
  output logic            sreq_sda_o
);

  // Timing diagram:
  //      __________     ___     ___     ___     ___     ___     ___
  // SCL            \___/   \___/   \___/   \___/   \___/   \___/   \___/
  //      ___         _______________________________
  // SDA     \______/_______/_______/_______/_______/--------------------
  //                      6       5       4       3       2       1
  //                                         _____________________________
  // TRX  ----------------------------------/_______/_______/_______/_____
  //
  //                                |
  // TRX can start monitoring ------
  //
  // TRX may start driving bit 3 of the arbitrable address header because at that point
  // it has both the IBI description and knowledge of the first 3 address bits to know whether
  // arbitration has yet been lost.

  logic scl_rise, scl_fall;
  prim_edge_detector #(.Width(1), .ResetValue('1), .EnSync(1'b0)) u_scl_edge (
    .clk_i              (clk_i),
    .rst_ni             (rst_ni),
    .d_i                (scl_i),
    .q_sync_o           (),
    .q_posedge_pulse_o  (scl_rise),
    .q_negedge_pulse_o  (scl_fall)
  );

  // TODO: We may need to introduce delays but the non-initial address bits may be sent in
  // push-pull mode by some Active Controllers, with Pure Bus timing.
  logic sda_sample, sda_drive, stopping;
  assign sda_sample = scl_rise;
  assign sda_drive  = scl_fall;

  // Keep track of whether arbitration has yet been lost.
  logic arb_lost_q, arb_lost_d;
  assign arb_lost_d = arb_lost_q | (sda_sample & (sda_i ^ sreq_sda_o));

  // Here we drive out the first 4 bits to ensure an overlap with the TRX driving and no glitches.
  // Control logic.
  logic [1:0] bit_cnt_q;
  logic active_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cnt_q   <= 2'b11;
      arb_lost_q  <= 1'b0;
      active_q    <= 1'b0;
    end else if (|{reset_i, start_i, !enable_i}) begin
      bit_cnt_q   <= 2'b11;
      arb_lost_q  <= 1'b0;
      active_q    <= enable_i & start_i;
    end else if (active_q) begin
      arb_lost_q  <= arb_lost_d;
      bit_cnt_q   <= bit_cnt_q - {1'b0, sda_drive};
      active_q    <= !stopping;
    end
  end

  assign stopping = sda_drive & ~|bit_cnt_q;

  // Select the appropriate bit from the IBI/CRR target address.
  logic addr_bit;
  always_comb begin
    case (bit_cnt_q)
      2'b00:   addr_bit = addr_i[3];
      2'b01:   addr_bit = addr_i[4];
      2'b10:   addr_bit = addr_i[5];
      default: addr_bit = addr_i[6];
    endcase
  end

  // Start request to the transceiver.
  // - this output must be high normally, in order to permit transmission on the SDA line.
  // - driving SDA low is a signal to the Active Controller to start clocking during the
  //   Bus Idle condition, so that we may send In-Band Interrupts, Hot-Join Requests etc.
  logic sreq_sda_od_en_q;
  logic sreq_sda_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sreq_sda_od_en_q  <= 1'b0;
      sreq_sda_q        <= 1'b1;
    end else if (reset_i | !enable_i) begin
      sreq_sda_od_en_q  <= 1'b0;
      sreq_sda_q        <= 1'b1;
    end else if (start_i) begin
      sreq_sda_od_en_q  <= 1'b1;
      sreq_sda_q        <= 1'b0;
    end else if (active_q & sda_drive) begin
      sreq_sda_od_en_q  <= !arb_lost_d & !stopping;
      sreq_sda_q        <= addr_bit | arb_lost_d;
    end
  end

  // SDA output contribution comes directly from flops; note that this signal must also be
  // returned high under any exceptional condition.
  assign sreq_sda_od_en_o = sreq_sda_od_en_q;
  assign sreq_sda_o = sreq_sda_q;

endmodule
