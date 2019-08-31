// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART Transmit Module
//

module uart_tx (
  input               clk_i,
  input               rst_ni,

  input               tx_enable,
  input               tick_baud_x16,
  input  logic        parity_enable,

  input               wr,
  input  logic        wr_parity,
  input   [7:0]       wr_data,
  output              idle,

  output logic        tx
);


  logic    [3:0] baud_div;
  logic          tick_baud;

  logic    [3:0] bit_cnt, bit_cnt_next;
  logic   [10:0] sreg, sreg_next;
  logic          tx_next;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      baud_div  <= 4'h0;
      tick_baud <= 1'b0;
    end else if (tick_baud_x16) begin
      {tick_baud, baud_div} <= {1'b0,baud_div} + 5'h1;
    end else begin
      tick_baud <= 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cnt <= 4'h0;
      sreg    <= 11'h7ff;
      tx      <= 1'b1;
    end else begin
      bit_cnt <= bit_cnt_next;
      sreg    <= sreg_next;
      tx      <= tx_next;
    end
  end

  always_comb begin
    if (!tx_enable) begin
      bit_cnt_next = 4'h0;
      sreg_next    = 11'h7ff;
      tx_next      = 1'b1;
    end else begin
      bit_cnt_next = bit_cnt;
      sreg_next    = sreg;
      tx_next      = tx;
      if (wr) begin
        sreg_next    = {1'b1, (parity_enable ? wr_parity : 1'b1), wr_data, 1'b0};
        bit_cnt_next = (parity_enable ? 4'd11 : 4'd10);
      end else if (tick_baud && (bit_cnt != 4'h0)) begin
        sreg_next    = {1'b1, sreg[10:1]};
        tx_next      = sreg[0];
        bit_cnt_next = bit_cnt - 4'h1;
      end
    end
  end

  assign idle = (tx_enable) ? (bit_cnt == 4'h0) : 1'b1;

endmodule
