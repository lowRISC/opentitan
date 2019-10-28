// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART Receive Module
//

module uart_rx (
  input           clk_i,
  input           rst_ni,

  input           rx_enable,
  input           tick_baud_x16,
  input           parity_enable,
  input           parity_odd,

  output logic    tick_baud,
  output logic    rx_valid,
  output [7:0]    rx_data,
  output logic    idle,
  output          frame_err,
  output          rx_parity_err,

  input           rx
);

  logic            rx_valid_q;
  logic   [10:0]   sreg_q, sreg_d;
  logic    [3:0]   bit_cnt_q, bit_cnt_d;
  logic    [3:0]   baud_div_q, baud_div_d;
  logic            tick_baud_d, tick_baud_q;
  logic            idle_d, idle_q;

  assign tick_baud = tick_baud_q;
  assign idle      = idle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sreg_q      <= 11'h0;
      bit_cnt_q   <= 4'h0;
      baud_div_q  <= 4'h0;
      tick_baud_q <= 1'b0;
      idle_q      <= 1'b1;
    end else begin
      sreg_q      <= sreg_d;
      bit_cnt_q   <= bit_cnt_d;
      baud_div_q  <= baud_div_d;
      tick_baud_q <= tick_baud_d;
      idle_q      <= idle_d;
    end
  end

  always_comb begin
    if (!rx_enable) begin
      sreg_d      = 11'h0;
      bit_cnt_d   = 4'h0;
      baud_div_d  = 4'h0;
      tick_baud_d = 1'b0;
      idle_d      = 1'b1;
    end else begin
      tick_baud_d = 1'b0;
      sreg_d      = sreg_q;
      bit_cnt_d   = bit_cnt_q;
      baud_div_d  = baud_div_q;
      idle_d      = idle_q;
      if (tick_baud_x16) begin
        {tick_baud_d, baud_div_d} = {1'b0,baud_div_q} + 5'h1;
      end

      if (idle_q && !rx) begin
        // start of char, sample in the middle of the bit time
        baud_div_d  = 4'd8;
        tick_baud_d = 1'b0;
        bit_cnt_d   = (parity_enable ? 4'd11 : 4'd10);
        sreg_d      = 11'h0;
        idle_d      = 1'b0;
      end else if (!idle_q && tick_baud_q) begin
        if ((bit_cnt_q == (parity_enable ? 4'd11 : 4'd10)) && rx) begin
          // must have been a glitch on the input, start bit is not set
          // in the middle of the bit time, abort
          idle_d    = 1'b1;
          bit_cnt_d = 4'h0;
        end else begin
          sreg_d    = {rx, sreg_q[10:1]};
          bit_cnt_d = bit_cnt_q - 4'h1;
          idle_d    = (bit_cnt_q == 4'h1);
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) rx_valid_q <= 1'b0;
    else         rx_valid_q <= tick_baud_q & (bit_cnt_q == 4'h1);

  end

  assign rx_valid      = rx_valid_q;
  assign rx_data       = parity_enable ? sreg_q[8:1] : sreg_q[9:2];
  //    (rx_parity     = sreg_q[9])
  assign frame_err     = rx_valid_q & ~sreg_q[10];
  assign rx_parity_err = parity_enable & rx_valid_q &
                         (^{sreg_q[9:1],parity_odd});

endmodule
