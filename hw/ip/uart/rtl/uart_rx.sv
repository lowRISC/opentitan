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


  logic   [10:0]   sreg, sreg_next;
  logic    [3:0]   bit_cnt, bit_cnt_next;
  logic    [3:0]   baud_div, baud_div_next;
  logic            tick_baud_next, idle_next;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      sreg      <= 11'h0;
      bit_cnt   <= 4'h0;
      baud_div  <= 4'h0;
      tick_baud <= 1'b0;
      idle      <= 1'b1;
    end else begin
      sreg      <= sreg_next;
      bit_cnt   <= bit_cnt_next;
      baud_div  <= baud_div_next;
      tick_baud <= tick_baud_next;
      idle      <= idle_next;
    end
  end

  always_comb begin
    if (!rx_enable) begin
      sreg_next      = 11'h0;
      bit_cnt_next   = 4'h0;
      baud_div_next  = 4'h0;
      tick_baud_next = 1'b0;
      idle_next      = 1'b1;
    end else begin
      tick_baud_next = 1'b0;
      sreg_next      = sreg;
      bit_cnt_next   = bit_cnt;
      baud_div_next  = baud_div;
      idle_next      = idle;
      if (tick_baud_x16) begin
        {tick_baud_next, baud_div_next} = {1'b0,baud_div} + 5'h1;
      end

      if (idle && !rx) begin
        // start of char, sample in the middle of the bit time
        baud_div_next  = 4'd8;
        tick_baud_next = 1'b0;
        bit_cnt_next   = (parity_enable ? 4'd11 : 4'd10);
        sreg_next      = 11'h0;
        idle_next      = 1'b0;
      end else if (!idle && tick_baud) begin
        if ((bit_cnt == (parity_enable ? 4'd11 : 4'd10)) && rx) begin
          // must have been a glitch on the input, start bit is not set
          // in the middle of the bit time, abort
          idle_next    = 1'b1;
          bit_cnt_next = 4'h0;
        end else begin
          sreg_next    = {rx, sreg[10:1]};
          bit_cnt_next = bit_cnt - 4'h1;
          idle_next    = (bit_cnt == 4'h1);
        end
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) rx_valid <= 1'b0;
    else         rx_valid <= tick_baud & (bit_cnt == 4'h1);
  end

  assign rx_data       = parity_enable ? sreg[8:1] : sreg[9:2];
  //    (rx_parity     = sreg[9])
  assign frame_err     = rx_valid & ~sreg[10];
  assign rx_parity_err = parity_enable & rx_valid &
                         (^{sreg[9:1],parity_odd});

endmodule
