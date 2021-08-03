// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager interface to kmac
//

module keymgr_cnt import keymgr_pkg::*; #(
  parameter int Width = 2,
  parameter bit OutSelDnCnt = 1, // 0 selects up count
  parameter keymgr_cnt_style_e CntStyle = CrossCnt
) (
  input clk_i,
  input rst_ni,
  input clr_i,
  input set_i,
  input [Width-1:0] set_cnt_i,
  input en_i,
  output logic [Width-1:0] cnt_o,
  output logic err_o
);

  localparam int CntCopies = (CntStyle == DupCnt) ? 2 : 1;

  typedef enum logic [1:0] {
    CmpInvalid = 2'b01,
    CmpValid   = 2'b10
  } cmp_valid_e;

  cmp_valid_e cmp_valid;
  logic [CntCopies-1:0][Width-1:0] up_cnt_d, up_cnt_d_buf;
  logic [CntCopies-1:0][Width-1:0] up_cnt_q;
  logic [Width-1:0] max_val;
  logic err;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      max_val <= '{default: '1};
    end else if (set_i && OutSelDnCnt) begin
      max_val <= set_cnt_i;
    end
  end

  for (genvar i = 0; i < CntCopies; i++) begin : gen_cnts
    // up-count
    assign up_cnt_d[i] = (clr_i)                        ? '0 :
                         (en_i & up_cnt_q[i] < max_val) ? up_cnt_q[i] + 1'b1 :
                                                          up_cnt_q[i];

    prim_buf #(
      .Width(Width)
    ) u_buf (
      .in_i(up_cnt_d[i]),
      .out_o(up_cnt_d_buf[i])
    );

    prim_flop #(
      .Width(Width),
      .ResetValue('0)
    ) u_cnt_flop (
      .clk_i,
      .rst_ni,
      .d_i(up_cnt_d_buf[i]),
      .q_o(up_cnt_q[i])
    );
  end

  if (CntStyle == CrossCnt) begin : gen_cross_cnt_hardening
    logic [Width-1:0] down_cnt;
    logic [Width-1:0] sum;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cmp_valid <= CmpInvalid;
      end else if (clr_i) begin
        cmp_valid <= CmpInvalid;
      end else if ((cmp_valid == CmpInvalid) && set_i) begin
        cmp_valid <= CmpValid;
      end
    end

    // down-count
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        down_cnt <= '0;
      end else if (clr_i) begin
        down_cnt <= '0;
      end else if (set_i) begin
        down_cnt <= set_cnt_i;
      end else if (en_i && down_cnt >'0) begin
        down_cnt <= down_cnt - 1'b1;
      end
    end

    logic msb;
    assign {msb, sum} = down_cnt + up_cnt_q[0];
    assign cnt_o = OutSelDnCnt ? down_cnt : up_cnt_q[0];
    assign err   = max_val != sum | msb;

  end else if (CntStyle == DupCnt) begin : gen_dup_cnt_hardening
    // duplicate count compare is always valid
    assign cmp_valid = CmpValid;
    assign cnt_o = up_cnt_q[0];
    assign err   = (up_cnt_q[0] != up_cnt_q[1]);
  end

  // if the compare flag is not a valid enum, treat it like an error.
  assign err_o = (cmp_valid == CmpValid)   ?  err :
                 (cmp_valid == CmpInvalid) ?  '0  : 1'b1;


endmodule // keymgr_cnt
