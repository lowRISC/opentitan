// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
module pinmux_wkup
  import pinmux_pkg::*;
  import pinmux_reg_pkg::*;
#(
  parameter int Cycles = 4
) (
  input                                 clk_i,
  input                                 rst_ni,
  input                                 wkup_en_i,
  input                                 filter_en_i,
  input  wkup_mode_e                    wkup_mode_i,
  input              [WkupCntWidth-1:0] wkup_cnt_th_i,
  input                                 pin_value_i,
  // Wakeup request pulse signal
  output logic                          aon_wkup_pulse_o
);

  ////////////////////////////
  // Optional Signal Filter //
  ////////////////////////////

  // This uses a lower value for filtering than GPIO since the always-on clock is slower. If the
  // filter is disabled, this reduces to a plain 2-stage flop synchronizer.
  logic filter_out_d, filter_out_q;
  prim_filter #(
    .AsyncOn(1), // Instantiate 2-stage synchronizer
    .Cycles(Cycles)
  ) u_prim_filter (
    .clk_i,
    .rst_ni,
    .enable_i(filter_en_i),
    .filter_i(pin_value_i),
    .filter_o(filter_out_d)
  );

  //////////////////////
  // Pattern Matching //
  //////////////////////

  logic rising, falling;
  assign falling = ~filter_out_d & filter_out_q;
  assign rising  = filter_out_d & ~filter_out_q;

  logic cnt_en, cnt_eq_th;
  logic [WkupCntWidth-1:0] cnt_d, cnt_q;
  assign cnt_d     = (cnt_eq_th) ? '0 : (cnt_en) ? cnt_q + 1'b1 : '0;

  assign cnt_eq_th = (cnt_q >= wkup_cnt_th_i);

  always_comb begin : p_mode
    aon_wkup_pulse_o = 1'b0;
    cnt_en           = 1'b0;
    if (wkup_en_i) begin
      unique case (wkup_mode_i)
        Negedge: begin
          aon_wkup_pulse_o = falling;
        end
        Edge: begin
          aon_wkup_pulse_o = rising | falling;
        end
        HighTimed: begin
          cnt_en = filter_out_d;
          aon_wkup_pulse_o = cnt_eq_th;
        end
        LowTimed: begin
          cnt_en = ~filter_out_d;
          aon_wkup_pulse_o = cnt_eq_th;
        end
        // Default to rising
        default: begin
          aon_wkup_pulse_o = rising;
        end
      endcase
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_aon_pattern
    if (!rst_ni) begin
      filter_out_q <= 1'b0;
      cnt_q        <= '0;
    end else begin
      filter_out_q <= filter_out_d;
      cnt_q        <= cnt_d;
    end
  end

endmodule : pinmux_wkup
