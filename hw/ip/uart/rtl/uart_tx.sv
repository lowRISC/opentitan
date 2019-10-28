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


  logic    [3:0] baud_div_q;
  logic          tick_baud_q;

  logic    [3:0] bit_cnt_q, bit_cnt_d;
  logic   [10:0] sreg_q, sreg_d;
  logic          tx_q, tx_d;

  assign tx = tx_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      baud_div_q  <= 4'h0;
      tick_baud_q <= 1'b0;
    end else if (tick_baud_x16) begin
      {tick_baud_q, baud_div_q} <= {1'b0,baud_div_q} + 5'h1;
    end else begin
      tick_baud_q <= 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      bit_cnt_q <= 4'h0;
      sreg_q    <= 11'h7ff;
      tx_q      <= 1'b1;
    end else begin
      bit_cnt_q <= bit_cnt_d;
      sreg_q    <= sreg_d;
      tx_q      <= tx_d;
    end
  end

  always_comb begin
    if (!tx_enable) begin
      bit_cnt_d = 4'h0;
      sreg_d    = 11'h7ff;
      tx_d      = 1'b1;
    end else begin
      bit_cnt_d = bit_cnt_q;
      sreg_d    = sreg_q;
      tx_d      = tx_q;
      if (wr) begin
        sreg_d    = {1'b1, (parity_enable ? wr_parity : 1'b1), wr_data, 1'b0};
        bit_cnt_d = (parity_enable ? 4'd11 : 4'd10);
      end else if (tick_baud_q && (bit_cnt_q != 4'h0)) begin
        sreg_d    = {1'b1, sreg_q[10:1]};
        tx_d      = sreg_q[0];
        bit_cnt_d = bit_cnt_q - 4'h1;
      end
    end
  end

  assign idle = (tx_enable) ? (bit_cnt_q == 4'h0) : 1'b1;

endmodule
